import argparse
import json
import pickle
from pathlib import Path

from benchmarks.rcpsp.psplib import PSPLibDataset, parse_rcpsp, rcpsp_model

import cpmpy as cp
from cpmpy.solvers.solver_interface import ExitStatus

from nested_explanations import find_explanation_sequence

RCPSP_ROOT = "benchmarks/rcpsp"
RCPSP_FAMILIES = ["j30", "j60", "j90", "j120"]

def download_psplib(root=RCPSP_ROOT, families=RCPSP_FAMILIES):
    """Download RCPSP benchmark instances from PSPLib if not already present."""
    for family in families:
        dataset = PSPLibDataset(variant="rcpsp", family=family, download=True, root=root)
        print(f"PSPLib rcpsp {family}: {len(dataset)} instances in {dataset.family_dir}")

def load_rcpsp_model(instance_name, family):
    dataset = PSPLibDataset(variant="rcpsp", family=family, transform=parse_rcpsp, download=False, root=RCPSP_ROOT)
    (table, capacities), metadata = dataset[instance_name]

    model, (start, makespan) = rcpsp_model(job_data=table, capacities=capacities)
    res = model.solve(solver="ortools", num_workers=1, time_limit=3600) # find optimal makespan, time limit of 1h

    if model.status().exitstatus != ExitStatus.OPTIMAL:
        raise ValueError(f"Could not solve instance {instance_name} in family {family} to optimality, skipping...")

    extra_lits = [makespan <= makespan.value()-1]
    return model, extra_lits

def load_pickled_model(fname):
    # nurse rostering instances are pickled as a (constraints, metadata) tuple
    with open(fname, "rb") as f:
        constraints, metadata = pickle.load(f)
    return cp.Model(constraints), [] # no extra literals


def _get_max_depth(sequence, depth=0):
    max_depth = depth
    for step in sequence:
        if "nested_explanation" in step:
            max_depth = max(max_depth, _get_max_depth(step["nested_explanation"], depth + 1))
    return max_depth

def _nb_of_steps(sequence):

    nb_steps = 0
    for step in sequence:
        nb_steps += 1
        if "nested_explanation" in step:
            nb_steps += _nb_of_steps(step["nested_explanation"])
    return nb_steps

def do_experiment(model: cp.Model,
                  extra_lits,
                  time_limit: int = 3600,
                  mus_solver: str = "exact",
                  mus_algo: str = "deletion") -> dict:
    """
    Compute a nested explanation sequence for the given model and extra literals.
    Returns a dictionary with the statistics of the experiment.
    """

    sequence, proof = find_explanation_sequence(model,
                                                extra_lits=extra_lits,
                                                time_limit=time_limit,
                                                mus_solver=mus_solver,
                                                mus_algo=mus_algo)

    # compute statistics of the sequence
    statistics = dict(
        sequence_length = len(sequence),
        max_depth = _get_max_depth(sequence),
        nb_of_steps = _nb_of_steps(sequence),
        proof_length = len(proof),
    )

    return statistics

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Run a nested explanation experiment")
    parser.add_argument("--download-psplib", action="store_true",
                        help="Download all RCPSP PSPLib benchmark families (j30, j60, j90, j120)")
    source = parser.add_mutually_exclusive_group()
    source.add_argument("--model", metavar="FILE", help="Path to a pickled model file (e.g. a nurse rostering instance)")
    source.add_argument("--family", help="RCPSP benchmark family (j30, j60, j90, j120)")
    parser.add_argument("--instance", help="RCPSP instance name or index (required with --family)")
    parser.add_argument("-o", "--output", metavar="FILE", help="Write results to this JSON file")
    parser.add_argument("--time-limit", type=int, default=3600)
    parser.add_argument("--mus-solver", default="exact")
    parser.add_argument("--mus-algo", default="deletion", choices=["deletion", "smus"])
    args = parser.parse_args()

    if args.download_psplib:
        download_psplib()
    elif args.model:
        model_path = Path(args.model)
        model, extra_lits = load_pickled_model(model_path)
        result_meta = {"model": str(model_path.resolve())}
        output_path = args.output or model_path.with_suffix(".json")
        print(f"Computing stepwise explanation sequence for {model_path}")
    elif args.family:
        if args.instance is None:
            parser.error("--instance is required when using --family")
        model, extra_lits = load_rcpsp_model(args.instance, args.family)
        result_meta = {"benchmark": "rcpsp", "family": args.family, "instance": args.instance}
        output_path = args.output or Path(f"rcpsp_{args.family}_{args.instance}.json")
        print(f"Computing stepwise explanation sequence for {args.family} instance {args.instance}")
    else:
        parser.error("one of --download-psplib, --model, or --family is required")

    if not args.download_psplib:
        statistics = do_experiment(model,
                                   extra_lits,
                                   time_limit=args.time_limit,
                                   mus_solver=args.mus_solver,
                                   mus_algo=args.mus_algo)

        result = {**result_meta, **statistics}
        with open(output_path, "w") as f:
            json.dump(result, f, indent=2)
        print(f"Wrote results to {output_path}")

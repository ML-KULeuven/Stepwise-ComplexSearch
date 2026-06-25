
import copy

def simplify_proof(proof, condition):
    """
        Simplify the proof based on the given condition.
        Resulting proof will have only steps that satisfy the condition.

        Used for example to remove steps with auxiliary variables or deriving complex expressions

    :param proof: parsed proof (list of dictionaries)
    :param condition: callable returning True or False given a proof step
    :return: processed proof
    """

    new_proof = []
    parent_dict = dict()  # id to list of (grand+)parents

    for i, step in enumerate(proof):

        if condition(step) is True: # ok, we can show this step
            new_uses = set()
            for id in step['reasons']:
                new_uses = new_uses.union(parent_dict.get(id, [id]))
            step = copy.copy(step)
            step['reasons'] = list(new_uses)
            new_proof.append(step)

        else: # we cannot show this step, need to replace future steps with reasons of this one
            assert step['id'] not in parent_dict
            tb_replaced_with = set()
            for id in step['reasons']:
                tb_replaced_with.update(parent_dict.get(id, [id]))
            parent_dict[step['id']] = tb_replaced_with

    return new_proof

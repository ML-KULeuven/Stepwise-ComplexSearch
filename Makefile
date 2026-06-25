.PHONY: install install-requirements install-pumpkin reinstall-pumpkin nurserostering rcpsp

PYTHON ?= python

install: install-requirements install-pumpkin

install-requirements:
	pip install -r requirements.txt
	pip install git+https://github.com/CPMpy/cpmpy.git@13dec1a6fe7066f3b7af991239d3142ab137a48c

install-pumpkin:
	@if pip show pumpkin-solver >/dev/null 2>&1; then \
		echo "pumpkin-solver is already installed, skipping (use 'make reinstall-pumpkin' to force)"; \
	else \
		$(MAKE) reinstall-pumpkin; \
	fi

reinstall-pumpkin:
	git submodule update --init --recursive pumpkin
	cd pumpkin && git checkout pumpkin-solver-v0.3.0
	cd pumpkin && \
	if git apply --check ../patches/disable_fixpoint_prop.patch >/dev/null 2>&1; then \
		git apply ../patches/disable_fixpoint_prop.patch && \
		echo "Applied pumpkin patch"; \
	else \
		echo "Patch already applied or cannot be applied cleanly"; \
	fi;
	pip uninstall pumpkin-solver -y
	cd pumpkin/pumpkin-solver-py && maturin develop --release

nurserostering:
	mkdir -p results/nurserostering
	for f in benchmarks/nr_musses/*.pickle; do \
		$(PYTHON) experiments.py --model "$$f" -o "results/nurserostering/$$(basename "$$f" .pickle).json"; \
	done

rcpsp:
	$(PYTHON) experiments.py --download-psplib
	@for family_dir in benchmarks/rcpsp/rcpsp/*/; do \
		family=$$(basename "$$family_dir"); \
		mkdir -p "results/rcpsp"; \
		for f in "$$family_dir"*.sm; do \
			instance=$$(basename "$$f" .sm); \
			$(PYTHON) experiments.py --family "$$family" --instance "$$instance" \
				-o "results/rcpsp/$${family}_$${instance}.json"; \
		done; \
	done

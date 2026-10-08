BEND ?= $(HOME)/.bend/bin/bend
SOURCES := $(shell find src tests -name '*.bend' -type f 2>/dev/null | LC_ALL=C sort)

.PHONY: test check proofs verdict bench clean

test:
	scripts/test.sh

check:
	@for f in $(SOURCES); do $(BEND) "$$f" --check-only || exit 1; done

proofs:
	@if [ -f PROOF.bend ]; then $(BEND) PROOF.bend; else echo "no PROOF.bend"; fi

verdict:
	$(BEND) PROOF.bend --verdict

bench:
	@if [ -f scripts/bench.sh ]; then scripts/bench.sh; else echo "no scripts/bench.sh"; fi

clean:
	rm -rf build

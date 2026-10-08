AGDA ?= agda
VERSION ?= $(shell date +%Y-%m-%d)

.PHONY: check html zip clean

# Typecheck everything from scratch and scan for unsafe features
check:
	AGDA=$(AGDA) ./scripts/check.sh

# Clickable HTML rendering of the code, starting at html/DLTT.Everything.html
html:
	$(AGDA) --html --html-dir=html DLTT/Everything.agda

# Clean archive for Zenodo in dist/
zip:
	AGDA=$(AGDA) ./scripts/make-zip.sh $(VERSION)

clean:
	rm -rf _build
	find DLTT -name '*.agdai' -delete

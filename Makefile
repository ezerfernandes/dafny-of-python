SHELL := /bin/sh

UV ?= uv
OPAM ?= opam
DUNE ?= dune
PYTHON ?= python
PYTEST ?= pytest
OCAML_VERSION ?= 4.14.2

UV_RUN := $(UV) run --frozen --
OPAM_EXEC := $(UV_RUN) $(OPAM) exec --
LOCAL_OPAM_BIN := $(CURDIR)/_opam/bin

ifneq ($(wildcard $(LOCAL_OPAM_BIN)/dune),)
OCAML_ENV := PATH="$(LOCAL_OPAM_BIN):$$PATH"
OCAML_EXEC := $(OCAML_ENV) $(LOCAL_OPAM_BIN)/dune
else
OCAML_ENV :=
OCAML_EXEC := $(OPAM_EXEC) $(DUNE)
endif

.PHONY: help setup uv-sync opam-switch opam-install build ocaml-build \
        python-test ocaml-test test python-coverage ocaml-coverage coverage \
        real-integration integration run clean

help:
	@printf '%s\n' \
	  'make setup           Install the locked Python and Opam dependencies' \
	  'make build           Build all OCaml targets' \
	  'make python-test    Run the pytest suite' \
	  'make ocaml-test     Run the Dune/Alcotest suite and CLI checks' \
	  'make test           Run Python and OCaml tests' \
	  'make coverage       Run Python and OCaml coverage gates' \
	  'make real-integration Run the real mypy/Dafny smoke test' \
	  'make integration     Build and run all integration checks' \
	  'make run FILE=x.py  Translate FILE with the CLI' \
	  'make clean           Remove generated build and coverage output'

uv-sync:
	$(UV) sync --frozen

opam-switch:
	@if test -x "$(LOCAL_OPAM_BIN)/dune"; then \
	  :; \
	else \
	  if ! $(OPAM) var root >/dev/null 2>&1; then \
	    $(OPAM) init --bare --disable-sandboxing --yes; \
	  fi; \
	  if $(OPAM) switch list --short | grep -Fxq .; then \
	    $(OPAM) switch set .; \
	  else \
	    $(OPAM) switch create . $(OCAML_VERSION) --yes; \
	  fi; \
	fi

opam-install: opam-switch
	@if test -x "$(LOCAL_OPAM_BIN)/dune"; then \
	  :; \
	else \
	  $(OPAM) install . --deps-only --locked --yes; \
	  $(OPAM) install alcotest.1.9.1 bisect_ppx.2.8.3 --yes; \
	fi

setup: uv-sync opam-install

build: ocaml-build

ocaml-build:
	$(OCAML_EXEC) build @all

python-test:
	$(UV_RUN) $(PYTEST) -q test/python

ocaml-test:
	$(OCAML_EXEC) runtest --force

test: python-test ocaml-test

python-coverage:
	$(UV_RUN) $(PYTEST) -q test/python \
		--cov=scripts --cov-branch --cov-report=term-missing --cov-fail-under=100

ocaml-coverage:
	@if test -x "$(LOCAL_OPAM_BIN)/dune"; then \
	  $(OCAML_ENV) ./scripts/coverage.sh; \
	else \
	  $(OPAM_EXEC) ./scripts/coverage.sh; \
	fi

coverage: python-coverage ocaml-coverage

real-integration: build
	$(OCAML_EXEC) build @real-integration

integration: test real-integration

run:
	@test -n "$(FILE)" || { printf '%s\n' 'Usage: make run FILE=program.py' >&2; exit 2; }
	$(OCAML_EXEC) exec src/bin/main.exe < "$(FILE)"

clean:
	$(OCAML_EXEC) clean
	/bin/rm -rf _coverage

# Checking for required tools.
ifeq (,$(shell command -v dune 2> /dev/null))
$(error "Compilation requires [dune].")
endif
ifeq (,$(shell command -v lem 2> /dev/null))
$(error "Compilation requires [lem].")
endif

# Trick to avoid printing the commands.
# To enable the printing of commands, use [make Q= ...],
Q = @

ifdef PROFILING
    DUNEFLAGS=--workspace=dune-workspace.profiling
else
    DUNEFLAGS=
endif

.PHONY: normal
normal: cerberus

.PHONY: all
all: cerberus cerberus-bmc cerberus-web #rustic

.PHONY: full-build
full-build: prelude-src
	@echo "[DUNE] full build"
	$(Q)dune build $(DUNEFLAGS)

.PHONY: util
util:
	@echo "[DUNE] library [$@]"
	$(Q)dune build $(DUNEFLAGS) _build/default/$@/$@.cma _build/default/$@/$@.cmxa
	ifdef PROFILING
		$(Q)dune build $(DUNEFLAGS) _build/profiling/$@/$@.cma _build/profiling/$@/$@.cmxa
		$(Q)dune build $(DUNEFLAGS) _build/profiling-auto/$@/$@.cma _build/profiling-auto/$@/$@.cmxa
	endif

.PHONY: cerberus
cerberus: prelude-src
	@echo "[DUNE] cerberus"
	$(Q)dune build $(DUNEFLAGS) cerberus-lib.install cerberus.install

.PHONY: test
test: prelude-src
	@echo "testing"
	dune exec coq/coqcaptest.exe

.PHONY: cerberus-bmc bmc
bmc: cerberus-bmc
cerberus-bmc: prelude-src
	@echo "[DUNE] cerberus-bmc"
	$(Q)dune build $(DUNEFLAGS) cerberus-lib.install cerberus-bmc.install

# .PHONY: rustic
# rustic: prelude-src
# 	@echo "[DUNE] $@"
# 	$(Q)dune build $(DUNEFLAGS) cerberus.install rustic.install

cheri: prelude-src
	@echo "[DUNE] cerberus-cheri"
	$(Q)dune build $(DUNEFLAGS) cerberus-lib.install cerberus-cheri.install

# combined goal to build both cerberus and cheri together as single dune run.
# building them separately form makefile causes them to run two confilcting
# dune builds in parallel
.PHONY: cerberus-with-cheri
cerberus-with-cheri: prelude-src
	@echo "[DUNE] cerberus-with-cheri"
	$(Q)dune build $(DUNEFLAGS) cerberus-lib.install cerberus.install cerberus-cheri.install

# .PHONY: cerberus-ocaml ocaml
# ocaml: cerberus-ocaml
# cerberus-ocaml: prelude-src
# 	@echo "[DUNE] $@"
# 	$(Q)dune build _build/default/backend/ocaml/driver/main.exe
# 	FIXME does not compile
# 	FIXME should generate rt-ocaml as a library
# 	@echo $(BOLD)INSTALLING Ocaml Runtime in ./_lib$(RESET)
# 	@mkdir -p _lib/rt-ocaml
# 	@cp backend/ocaml/runtime/META _lib/rt-ocaml
# 	@cp backend/ocaml/runtime/_build/rt_ocaml.a \
# 		   backend/ocaml/runtime/_build/rt_ocaml.cma \
# 			 backend/ocaml/runtime/_build/rt_ocaml.cmxa _lib/rt-ocaml
# 	@cp backend/ocaml/runtime/_build/*.cmi _lib/rt-ocaml
# 	@cp backend/ocaml/runtime/_build/*.cmx _lib/rt-ocaml
# 	@cp backend/ocaml/runtime/_build/src/*.cmi _lib/rt-ocaml
# 	@cp backend/ocaml/runtime/_build/src/*.cmx _lib/rt-ocaml

tmp/:
	@echo "[MKDIR] tmp"
	$(Q)mkdir -p tmp

config.json: tools/config.json
	@echo "[CP] $< → $@"
	@cp $< $@

.PHONY: cerberus-web web
web: cerberus-web
cerberus-web: prelude-src config.json tmp/
	@echo "[DUNE] web"
	$(Q)dune build $(DUNEFLAGS) cerberus-lib.install cerberus.install cerberus-web.install
#	@cp -L _build/default/backend/web/instance.exe webcerb.concrete
#	@cp -L _build/default/backend/web/instance_symbolic.exe webcerb.symbolic
#	@cp -L _build/default/backend/web/instance_vip.exe webcerb.vip
#	@cp -L _build/default/backend/web/web.exe cerberus-webserver

.PHONY: ui
ui:
	make -C public

# # Elaboration PP stuff
# elab_pp:
# 	@echo "[MKDIR] $(PRELUDE_SRC_DIR)"
# 	$(Q)mkdir -p generated_tex
# 	$(Q)lem -wl ign -wl_rename warn -wl_pat_red err -wl_pat_exh warn \
# 	-outdir generated_tex -cerberus_pp -tex \
# 	$(addprefix -i ,$(filter-out frontend/model/translation.lem,$(LEM_SRC))) frontend/model/translation.lem
# 	cd generated_tex; lualatex Translation.tex

.PHONY: clean
clean:
	$(Q)rm -f coq/*.{glob,vo,vok}
	$(Q)rm -f webcerb.concrete webcerb.symbolic cerberus-webserver
	$(Q)dune clean

.PHONY: distclean
distclean: clean
	$(Q)rm -rf tmp config.json

.PHONY: cerberus-lib
cerberus-lib:
	@echo "[DUNE] cerberus-lib"
	$(Q)dune build -p cerberus-lib

.PHONY: install_lib
install_lib: cerberus-lib
	@echo "[DUNE] install cerberus-lib"
	$(Q)dune install cerberus-lib

.PHONY: install
install: install_lib cerberus
	@echo "[DUNE] install cerberus"
	$(Q)dune install cerberus

.PHONY: install-cheri
install-cheri: install_lib
	@echo "[DUNE] install cerberus-cheri"
	$(Q)dune install cerberus-cheri

.PHONY: uninstall
uninstall: cerberus
	@echo "[DUNE] uninstall cerberus"
	$(Q)dune uninstall cerberus

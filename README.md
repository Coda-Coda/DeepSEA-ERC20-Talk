# Build instructions

1. Clone with submodules `git clone --recurse-submodules https://github.com/Coda-Coda/Alectryon-slides.git` (or `git submodule update --init --recursive` if already cloned).
2. Get [Nix](https://nixos.org)
2. `cd Alectryon-slides`
3. Edit `slides.rst` so that in line 8 the paths match your system instead of `/home/daniel/Code/Talk-ERC20-DeepSEA-Alectryon/`
4. `cd PhD-Thesis-Code-Artefact` # See README.md
5. `nix-shell`
6. `make`
7. `cd ..`
8.  `nix-shell`
9.  `make docs`
10. Open `docs/index.html`
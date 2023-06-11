# Build instructions

1. Clone with submodules `git clone --recurse-submodules https://github.com/Coda-Coda/Alectryon-slides.git` (or `git submodule update --init --recursive` if already cloned).
2. Get [Nix](https://nixos.org)
2. `cd Alectryon-slides`
4. Edit `slides.rst` so that in line 8 the path matches your system instead of /home/daniel/Documents/Code/research/Eth-Eng-Grp-Talk-2023
5. `cd contracts` # See README.md
6. `nix-build`
7. `nix-shell`
8. `./compile-coq Crowdfunding` # Don't include ".ds"
9. `./compile-coq trivial` # Don't include ".ds"
10. `exit`
11. `cd ..`
12. `nix-shell`
13. `make docs`
14. Open `docs/index.html`
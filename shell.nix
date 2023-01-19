let pkgs = import (
  builtins.fetchTarball {
  name = "nixpkgs-21.05-pinned";
  url = "https://github.com/nixos/nixpkgs/archive/61ac4169922ca62d00bfe7f28dae6e1f27fd9c89.tar.gz";
  sha256 = "05rjb4xx2m2qqp94x39k8mv447njvyqv1zk6kshkg0j9q4hcq8lf";
}) {}; in

let
  my-python-packages = with pkgs; python-packages: with python-packages; [
    alectryon
    pygments
    lxml
    sphinx
  ]; 
  python-with-my-packages = with pkgs; python3.withPackages my-python-packages;
in

pkgs.mkShell {
  buildInputs = with pkgs; [ 
      # texlive.combined.scheme-full
      coq_8_14
      coqPackages_8_14.serapi
      python-with-my-packages
      pdfpc
      hovercraft
      inkscape
    ];
  shellHook = ''
    
  '';
}
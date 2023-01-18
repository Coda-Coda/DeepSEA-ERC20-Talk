let pkgs = import (
  builtins.fetchTarball {
  name = "nixpkgs-21.05-pinned";
  url = "https://github.com/nixos/nixpkgs/archive/92f9580a4c369b4b51a7b6a5e77da43720134c9f.tar.gz";
  sha256 = "0w9bz4f2bmkj4a59n4z279zcgs9clyc40a4ny312rafyaknzghvw";
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
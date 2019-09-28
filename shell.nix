{ nixpkgs ? import <nixpkgs> {} }:
let
  inherit (nixpkgs) pkgs;
in pkgs.stdenv.mkDerivation {
  name = "spotter-env";
  buildInputs = with pkgs; [
    git gist
    rlwrap
    ocamlformat
    ocaml ] ++ (with ocamlPackages; [
      utop core findlib camomile zarith
  ]);
}

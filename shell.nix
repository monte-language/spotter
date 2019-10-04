{ nixpkgs ? import (builtins.fetchTarball {
  name = "spotter-pinned-nixpkgs";
  url = https://github.com/NixOS/nixpkgs/archive/0137b08bd1070a22564bf67bb7a678d2a6a60452.tar.gz;
  sha256 = "11806x69zxmmjhpv4cvpii2f51gqyd8yivdk7pv6nmlsc3d349yv";
}) {} }:
let
  inherit (nixpkgs) pkgs;
  ocamlPackages = pkgs.ocamlPackages_latest;
in pkgs.stdenv.mkDerivation {
  name = "spotter-env";
  buildInputs = with pkgs; [
    git gist
    rlwrap
    ocamlformat
    ] ++ (with ocamlPackages; [
      ocaml utop core findlib camomile zarith
  ]);
}

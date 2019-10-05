let
  pkgs = import (builtins.fetchTarball {
    name = "spotter-pinned-nixpkgs";
    url = https://github.com/NixOS/nixpkgs/archive/0137b08bd1070a22564bf67bb7a678d2a6a60452.tar.gz;
    sha256 = "11806x69zxmmjhpv4cvpii2f51gqyd8yivdk7pv6nmlsc3d349yv";
  }) {};
  ocamlPackages = pkgs.ocamlPackages_latest;
  spotter = pkgs.stdenv.mkDerivation rec {
    name = "spotter";
    version = "0-git";
    src = ./.;
    buildInputs = with ocamlPackages;
      [ ocaml ocamlbuild findlib camomile zarith ];
    buildPhase = ''
      ocamlbuild -use-ocamlfind -pkgs camomile,zarith \
        -tag debug \
        spotter.byte spotter.native
    '';
    installPhase = ''
      mkdir -p $out/bin/
      cp _build/spotter.byte $out/bin/
      cp _build/spotter.native $out/bin/spotter
    '';
  };
in
  { inherit spotter; }

{ pkgs ? import <nixpkgs> {}, ...} :
let
  idrisWithPackages = import <nixpkgs/pkgs/development/idris-modules/with-packages.nix> { stdenv = pkgs.stdenv; idris = pkgs.idris; };
  idris = idrisWithPackages ([ pkgs.idrisPackages.builtins pkgs.idrisPackages.contrib pkgs.idrisPackages.lightyear ]);
in pkgs.stdenv.mkDerivation {
  name = "idris-microkanren";
  buildInputs = [ idris ];
  buildPhase = ''
    idris --build plm.ipkg
  '';
  installPhase = ''
    mkdir -p $out
    cp plm $out/plm
  '';
}

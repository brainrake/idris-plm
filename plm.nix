{ build-idris-package
, fetchFromGitHub
, contrib
, lightyear
, lib
}:
build-idris-package  {
  name = "plm";
  version = "0.0.0";
  ipkgName = "plm";
  idrisDeps = [ contrib lightyear ];
  src = ./.;
  meta = {
    description = "Principia Logico-Metaphysica in Idris";
    homepage = https://github.com/brainrape/idris-plm;
    license = lib.licenses.mit;
    maintainers = [ lib.maintainers.brainrape ];
  };
}
  /* buildPhase = ''
    idris --build plm.ipkg
  '';
  installPhase = ''
    mkdir -p $out
    cp plm $out/plm
  '';
} */

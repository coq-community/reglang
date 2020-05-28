{ pkgs ? (import <nixpkgs> {}), coq-version-or-url, shell ? false }:

let
  coq-version-parts = builtins.match "([0-9]+).([0-9]+)" coq-version-or-url;
  coqPackages =
    if coq-version-parts == null then
      pkgs.mkCoqPackages (import (fetchTarball coq-version-or-url) {})
    else
      pkgs."coqPackages_${builtins.concatStringsSep "_" coq-version-parts}";
in

with coqPackages;

let
  ssreflect =
    coqPackages.ssreflect.overrideAttrs(_: rec {
      name = "coq-${coq.coq-version}-ssreflect-${version}";
      version = "dev";
      src = fetchTarball "https://github.com/math-comp/math-comp/tarball/master";
    });
in

pkgs.stdenv.mkDerivation {

  name = "reglang";

  propagatedBuildInputs = [
    coq
    ssreflect
  ];

  src = if shell then null else ./.;

  installFlags = "COQMF_COQLIB=$(out)/lib/coq/${coq.coq-version}/";
}

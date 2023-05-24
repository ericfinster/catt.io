with import <nixpkgs> { };

let
  ocaml_inputs = [ dune_3 ocaml opam ] ++ (with ocamlPackages; [ fmt js_of_ocaml js_of_ocaml-ppx menhir sedlex ]);
in
stdenv.mkDerivation {
  pname = "catt";
  version = "0.2.0";
  src = ./.;
  buildInputs = ocaml_inputs;
  buildPhase = ''
    rm -rf result
    dune clean
    dune build
  '';
  installPhase = ''
    mkdir -p $out/bin
    install -Dm755 _build/default/bin/catt.exe $out/bin
    mkdir -p $out/web
    install -Dm644 _build/default/web/cattweb.bc.js $out/web
  '';
}


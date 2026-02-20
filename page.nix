{ mkDerivation, multimarkdown, standard-library }:

mkDerivation {
  pname = "strict-group-theory";
  version = "master";

  src = ./.;

  LC_ALL = "en_GB.UTF-8";

  buildInputs = [ standard-library."1.3" multimarkdown ];

  buildPhase = ''
    agda --html --html-highlight=auto *.lagda.md --css /css/Agda.css
    mmd html/*.md
    mv html/strict-group-theory.html html/index.html
  '';

  installPhase = ''
    mkdir -p $out
    cp html/*.html $out
  '';
}

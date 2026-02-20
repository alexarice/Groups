{
  description = "Agda flake";

  inputs = {
    all-agda.url = "github:alexarice/all-agda";
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgsold.url = "github:nixos/nixpkgs/8c5d37129fc5097d9fb52e95fb07de75392d1c3c";
  };

  outputs = { self, nixpkgsold, all-agda, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
    let
      agdaPackages = all-agda.legacyPackages."x86_64-linux".agdaPackages-2_6_1;
    in {
      packages = rec {
        page = agdaPackages.callPackage ./page.nix {
          inherit (nixpkgsold.legacyPackages."${system}") multimarkdown;
        };
        default = page;
      };
    }
  );
}

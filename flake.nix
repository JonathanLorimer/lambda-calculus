{
  description = "lambda-calculus";

  inputs = {
    # Nix Inputs
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
  };

  outputs = {
    self,
    nixpkgs,
  }: let
    forAllSystems = function:
      nixpkgs.lib.genAttrs [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ] (system:
        function rec {
          inherit system;
          pkgs = nixpkgs.legacyPackages.${system};
          hsPkgs = pkgs.haskellPackages.override {
            overrides = hfinal: hprev: {
              lambda-calculus = hfinal.callCabal2nix "lambda-calculus" ./. {};
            };
          };
        });
  in {
    # nix fmt
    formatter = forAllSystems ({pkgs, ...}: pkgs.alejandra);

    # nix develop
    devShell = forAllSystems ({
      hsPkgs,
      pkgs,
      ...
    }:
      hsPkgs.shellFor {
        # withHoogle = true;
        packages = p: [
          p.lambda-calculus
        ];
        buildInputs = with pkgs;
          [
            hsPkgs.haskell-language-server
            haskellPackages.cabal-install
            cabal2nix
            haskellPackages.ghcid
            haskellPackages.fourmolu
            haskellPackages.cabal-fmt
          ]
          ++ (builtins.attrValues (import ./scripts.nix {s = pkgs.writeShellScriptBin;}));
      });

    # nix build
    packages = forAllSystems ({hsPkgs, ...}: {
      lambda-calculus = hsPkgs.lambda-calculus;
      default = hsPkgs.lambda-calculus;
    });

    # You can't build the lambda-calculus package as a check because of IFD in cabal2nix
    checks = {};

    # nix run
    apps = forAllSystems ({system, ...}: {
      lambda-calculus = {
        type = "app";
        program = "${self.packages.${system}.lambda-calculus}/bin/lambda-calculus";
      };
      default = self.apps.${system}.lambda-calculus;
    });
  };
}

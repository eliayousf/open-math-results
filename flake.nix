{
  description = "Lean and Python environment for open mathematics";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";

  outputs = { nixpkgs, ... }: {
    devShells = nixpkgs.lib.genAttrs
      [ "aarch64-darwin" "x86_64-darwin" "aarch64-linux" "x86_64-linux" ]
      (system: let pkgs = nixpkgs.legacyPackages.${system}; in {
        default = pkgs.mkShell {
          packages = [ pkgs.elan pkgs.python3 ];
          shellHook = ''
            export ELAN_HOME="''${ELAN_HOME:-$(git rev-parse --show-toplevel)/.elan}"
          '';
        };
      });
  };
}

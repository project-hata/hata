# haskell/stack integration from https://docs.haskellstack.org/en/stable/nix_integration/

{
  description = "A basic flake with a shell";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = nixpkgs.legacyPackages.${system};
      libPath = with pkgs; lib.makeLibraryPath [
        libGL
        # libxkbcommon
        wayland
        xorg.libX11
        xorg.libXcursor
        xorg.libXi
        xorg.libXrandr
        zlib
      ];

      hPkgs =
          pkgs.haskell.packages."ghc902"; # need to match Stackage LTS version
                                           # from stack.yaml resolver


      # Wrap Stack to work with our Nix integration. We don't want to modify
      # stack.yaml so non-Nix users don't notice anything.
      # - no-nix: We don't want Stack's way of integrating Nix.
      # --system-ghc    # Use the existing GHC on PATH (will come from this Nix file)
      # --no-install-ghc  # Don't try to install GHC if no matching GHC found on PATH
      stack-wrapped = pkgs.symlinkJoin {
        name = "stack"; # will be available as the usual `stack` in terminal
        paths = [ pkgs.stack ];
        buildInputs = [ pkgs.makeWrapper ];
        postBuild = ''
            wrapProgram $out/bin/stack \
              --add-flags "\
                --no-nix \
                --system-ghc \
                --no-install-ghc \
              "
          '';
      };

    in {
      devShell = pkgs.mkShell {
        nativeBuildInputs = with pkgs; [ bashInteractive pkg-config ];
        buildInputs = with pkgs; [
          cmake
          fontconfig
          zlib.dev
          stack-wrapped
          hPkgs.ghc
          # xorg.libX11
          # xorg.libXcursor
          # xorg.libXrandr
          # xorg.libXi
          # libGL
          # mesa
        ];
        LD_LIBRARY_PATH = libPath;
      };
    });
}

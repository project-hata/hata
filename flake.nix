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
      ];

    in {
      devShell = pkgs.mkShell {
        nativeBuildInputs = with pkgs; [ bashInteractive pkg-config ];
        buildInputs = with pkgs; [
          cmake
          fontconfig
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

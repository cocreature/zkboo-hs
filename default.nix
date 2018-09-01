{ rev ? "4477cf04b6779a537cdb5f0bd3dd30e75aeb4a3b",
  outputSha256 ? "1i39wsfwkvj9yryj8di3jibpdg3b3j86ych7s9rb6z79k08yaaxc"
}:
let
  nixpkgs = builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    sha256 = outputSha256;
  };
  pkgs = import nixpkgs {};
  src = pkgs.lib.cleanSourceWith {
    src = pkgs.lib.cleanSource ./.;
    filter = path: type:
      let base = baseNameOf path;
      in !(pkgs.lib.hasPrefix ".ghc.environment." base) &&
         !(pkgs.lib.hasSuffix ".nix" base);
  };
  haskellPackages = pkgs.haskell.packages.ghc843.override(oldAttrs: {
    overrides = self: super: {
      zkboo-hs = super.callCabal2nix "zkboo-hs" src {};
    };
  });
in
haskellPackages.zkboo-hs

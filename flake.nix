{
  description = "A formalization in Coq of the Haskell pipes library, proving nearly all its laws";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    coq-haskell-src = {
      url = "github:jwiegley/coq-haskell";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, coq-haskell-src }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        coqPkgs = pkgs.coqPackages_8_16;
        coqVersion = coqPkgs.coq.coq-version;

        coq-haskell = coqPkgs.mkCoqDerivation {
          pname = "coq-haskell";
          version = "dev";
          src = coq-haskell-src;
        };

        coq-pipes = coqPkgs.mkCoqDerivation {
          pname = "coq-pipes";
          version = "dev";
          src = self;
          propagatedBuildInputs = [ coq-haskell ];
          enableParallelBuilding = false;
        };

      in {
        packages = {
          default = coq-pipes;
          inherit coq-haskell;

          timed = coq-pipes.overrideAttrs (old: {
            pname = "coq-pipes-timed";
            buildPhase = ''
              make -j''${NIX_BUILD_CORES:-1} TIMED=1 2>&1 | tee timing.log
            '';
            postInstall = ''
              mkdir -p $out/share/coq-pipes
              cp timing.log $out/share/coq-pipes/
            '';
          });
        };

        devShells.default = pkgs.mkShell {
          packages = [
            pkgs.lefthook
            pkgs.perl
          ];
          inputsFrom = [ coq-pipes ];
          shellHook = ''
            lefthook install 2>/dev/null || true
          '';
        };

        checks = {
          build = coq-pipes;

          no-admitted = pkgs.runCommand "coq-pipes-no-admitted" {
            src = self;
          } ''
            cd $src
            if find src -name '*.v' ! -name Extract.v -print0 | \
               xargs -0 grep -E -l '^\s*(Abort|Admitted)\.' 2>/dev/null; then
              echo "ERROR: Found admitted or aborted proofs"
              exit 1
            fi
            touch $out
          '';

          trailing-whitespace = pkgs.runCommand "coq-pipes-trailing-whitespace" {
            src = self;
          } ''
            cd $src
            if find src -name '*.v' -print0 | \
               xargs -0 grep -Pn '\s+$' 2>/dev/null; then
              echo "ERROR: Found trailing whitespace"
              exit 1
            fi
            touch $out
          '';

          coqchk = pkgs.runCommand "coq-pipes-coqchk" {
            nativeBuildInputs = [ coqPkgs.coq ];
            COQPATH = builtins.concatStringsSep ":" [
              "${coq-pipes}/lib/coq/${coqVersion}/user-contrib"
              "${coq-haskell}/lib/coq/${coqVersion}/user-contrib"
            ];
          } ''
            coqchk \
              P.Pipes \
              P.Pipes.Core \
              P.Pipes.Internal \
              P.Pipes.Prelude \
              P.Pipes.Extras
            touch $out
          '';
        };
      }
    );
}

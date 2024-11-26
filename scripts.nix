{s}: 
{
  ghcidScript = s "dev" "ghcid --command 'cabal new-repl lib:lambda-calculus' --allow-eval --warnings";
  testScript = s "test" "cabal run test:lambda-calculus-tests";
  hoogleScript = s "hgl" "hoogle serve";
}

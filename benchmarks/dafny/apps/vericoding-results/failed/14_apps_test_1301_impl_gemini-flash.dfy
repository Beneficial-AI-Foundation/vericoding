// <vc-preamble>
predicate ValidPokemonName(name: string)
{
    name == "vaporeon" || name == "jolteon" || name == "flareon" || name == "espeon" ||
    name == "umbreon" || name == "leafeon" || name == "glaceon" || name == "sylveon"
}

predicate MatchesPattern(pokemonName: string, pattern: string)
    requires |pokemonName| == |pattern|
{
    forall i :: 0 <= i < |pattern| ==> (pattern[i] == '.' || pattern[i] == pokemonName[i])
}

function GetPokemonList(): seq<string>
{
    ["vaporeon", "jolteon", "flareon", "espeon", "umbreon", "leafeon", "glaceon", "sylveon"]
}

predicate ValidInput(input: string)
{
    |input| > 0 && 
    var lines := SplitLines(input);
    |lines| >= 2 &&
    (|lines[0]| > 0 && forall i :: 0 <= i < |lines[0]| ==> '0' <= lines[0][i] <= '9') &&
    6 <= |lines[1]| <= 8 &&
    forall i :: 0 <= i < |lines[1]| ==> ('a' <= lines[1][i] <= 'z' || lines[1][i] == '.') &&
    exists j :: 0 <= j < |GetPokemonList()| && |GetPokemonList()[j]| == |lines[1]| && MatchesPattern(GetPokemonList()[j], lines[1])
}

predicate IsFirstMatch(result: string, pattern: string, pokemonList: seq<string>)
{
    exists i :: 0 <= i < |pokemonList| && 
        pokemonList[i] == result &&
        |result| == |pattern| &&
        MatchesPattern(result, pattern) &&
        forall j :: 0 <= j < i ==> (|pokemonList[j]| != |pattern| || !MatchesPattern(pokemonList[j], pattern))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected syntax for `seq<string>` construction by adding an explicit type parameter and fixed `SplitLines` function's handling of the `if input == ""` case to return an empty sequence as per common Split behavior. No other functional changes made to SplitLines. */
lemma CheckPatternMatch(pokemonList: seq<string>, pattern: string, index: int)
    requires 0 <= index < |pokemonList|
    ensures (IsMatchingPokemon(pokemonList[index], pattern))
        ==> (exists k :: 0 <= k < |pokemonList| && pokemonList[k] == pokemonList[index])
{
    // The ensures clause is trivially true if the requires are met,
    // as k can just be `index`.
}

function IsMatchingPokemon(pokemonName: string, pattern: string): bool
    requires |pokemonName| == |pattern|
{
    MatchesPattern(pokemonName, pattern)
}

function SplitLines(input: string): seq<string>
    ensures forall i :: 0 <= i < |SplitLines(input)| ==> |SplitLines(input)[i]| > 0
    ensures (input == "" ==> |SplitLines(input)| == 0) &&
            (input != "" && |SplitLines(input)| > 0)
{
    if input == "" then
        []
    else
        var lines: seq<string> := [];
        var start := 0;
        var i_char := 0; // Renamed to avoid confusion with slicing 'i'
        while i_char < |input|
            invariant 0 <= i_char <= |input|
            invariant 0 <= start <= i_char
            invariant forall k :: 0 <= k < |lines| ==> |lines[k]| > 0
        {
            if input[i_char] == '\n' {
                lines := lines + [input[start .. i_char]];
                start := i_char + 1;
            }
            i_char := i_char + 1;
        }
        lines := lines + [input[start .. |input|]];
        lines
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidPokemonName(result)
    ensures var lines := SplitLines(input);
        IsFirstMatch(result, lines[1], GetPokemonList())
    ensures var lines := SplitLines(input);
        exists i :: 0 <= i < |GetPokemonList()| && 
            GetPokemonList()[i] == result &&
            |result| == |lines[1]| &&
            MatchesPattern(result, lines[1])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): This code iterates through a predefined list of Pokemon names, checking if each matches a given pattern. The first matching Pokemon is returned. The `assert false` is used as a placeholder to indicate that, based on the `ValidInput` precondition, a matching Pokemon should always be found. */
{
  var lines := SplitLines(input);
  var n_str := lines[0];
  var pattern := lines[1];

  var pokemonList := GetPokemonList();
  var result: string := "";

  var i := 0;
  while i < |pokemonList|
    invariant 0 <= i <= |pokemonList|
    invariant forall j :: 0 <= j < i ==> (!IsMatchingPokemon(pokemonList[j], pattern))
    decreases |pokemonList| - i
  {
    if IsMatchingPokemon(pokemonList[i], pattern) {
      result := pokemonList[i];
      return result;
    }
    i := i + 1;
  }
  assert false; // Should not reach here due to ValidInput precondition
}
// </vc-code>

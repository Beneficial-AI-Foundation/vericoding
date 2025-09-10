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

// <vc-helpers>
function IndexOf(s: string, c: char): int
{
    if |s| == 0 then -1
    else if s[0] == c then 0
    else
        var rest := IndexOf(s[1..], c);
        if rest == -1 then -1 else 1 + rest
}

function SplitLines(s: string): seq<string>
{
    if |s| == 0 then []
    else
        var index := IndexOf(s, '\n');
        if index == -1 then [s]
        else [s[0..index]] + SplitLines(s[index+1..])
}

lemma LemmaMatchesPattern(pokemonName: string, pattern: string)
    requires |pokemonName| == |pattern|
    requires forall i :: 0 <= i < |pattern| ==> (pattern[i] == '.' || pattern[i] == pokemonName[i])
    ensures MatchesPattern(pokemonName, pattern)
{
    reveal MatchesPattern();
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
{
    var lines := SplitLines(input);
    var pattern := lines[1];
    var pokemonList := GetPokemonList();
    var i := 0;
    while i < |pokemonList|
        invariant 0 <= i <= |pokemonList|
        invariant forall j :: 0 <= j < i ==> (|pokemonList[j]| != |pattern| || !MatchesPattern(pokemonList[j], pattern))
        invariant exists j :: i <= j < |pokemonList| && |pokemonList[j]| == |pattern| && MatchesPattern(pokemonList[j], pattern)
    {
        if |pokemonList[i]| == |pattern| {
            var k := 0;
            var valid := true;
            while k < |pattern| && valid
                invariant 0 <= k <= |pattern|
                invariant valid ==> forall j :: 0 <= j < k ==> (pattern[j] == '.' || pattern[j] == pokemonList[i][j])
            {
                if pattern[k] != '.' && pattern[k] != pokemonList[i][k] {
                    valid := false;
                }
                k := k + 1;
            }
            if valid {
                LemmaMatchesPattern(pokemonList[i], pattern);
                return pokemonList[i];
            }
        }
        i := i + 1;
    }
    assert false;
}
// </vc-code>


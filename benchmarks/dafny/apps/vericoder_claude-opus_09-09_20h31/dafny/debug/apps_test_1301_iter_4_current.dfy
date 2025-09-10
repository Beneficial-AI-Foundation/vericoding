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
function SplitLines(input: string): seq<string>
{
    SplitLinesHelper(input, 0, [], "")
}

function SplitLinesHelper(input: string, i: int, lines: seq<string>, currentLine: string): seq<string>
    requires 0 <= i <= |input|
    decreases |input| - i
{
    if i == |input| then
        lines + [currentLine]
    else if input[i] == '\n' then
        SplitLinesHelper(input, i + 1, lines + [currentLine], "")
    else
        SplitLinesHelper(input, i + 1, lines, currentLine + [input[i]])
}

lemma MatchingPokemonExists(pattern: string)
    requires 6 <= |pattern| <= 8
    requires forall i :: 0 <= i < |pattern| ==> ('a' <= pattern[i] <= 'z' || pattern[i] == '.')
    requires exists j :: 0 <= j < |GetPokemonList()| && |GetPokemonList()[j]| == |pattern| && MatchesPattern(GetPokemonList()[j], pattern)
    ensures exists i :: 0 <= i < |GetPokemonList()| && 
        |GetPokemonList()[i]| == |pattern| &&
        MatchesPattern(GetPokemonList()[i], pattern) &&
        ValidPokemonName(GetPokemonList()[i])
{
    var pokemonList := GetPokemonList();
    assert pokemonList == ["vaporeon", "jolteon", "flareon", "espeon", "umbreon", "leafeon", "glaceon", "sylveon"];
    
    var j :| 0 <= j < |pokemonList| && |pokemonList[j]| == |pattern| && MatchesPattern(pokemonList[j], pattern);
    
    assert ValidPokemonName(pokemonList[j]);
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
    
    // From precondition, we know a matching Pokemon exists
    var witness :| 0 <= witness < |pokemonList| && |pokemonList[witness]| == |pattern| && MatchesPattern(pokemonList[witness], pattern);
    
    var i := 0;
    while i < |pokemonList|
        invariant 0 <= i <= |pokemonList|
        invariant forall j :: 0 <= j < i ==> (|pokemonList[j]| != |pattern| || !MatchesPattern(pokemonList[j], pattern))
        invariant i < |pokemonList| ==> exists k :: i <= k < |pokemonList| && |pokemonList[k]| == |pattern| && MatchesPattern(pokemonList[k], pattern)
    {
        if |pokemonList[i]| == |pattern| && MatchesPattern(pokemonList[i], pattern) {
            result := pokemonList[i];
            assert IsFirstMatch(result, pattern, pokemonList);
            MatchingPokemonExists(pattern);
            return;
        }
        // Before incrementing, establish that if a match exists, it's after index i
        assert |pokemonList[i]| != |pattern| || !MatchesPattern(pokemonList[i], pattern);
        assert witness >= i;
        if witness == i {
            // This is a contradiction since pokemonList[i] doesn't match but witness does
            assert false;
        }
        assert witness > i;
        i := i + 1;
    }
    
    // This should be unreachable due to the loop invariant
    assert i == |pokemonList|;
    assert !(i < |pokemonList|);
    assert false;
}
// </vc-code>


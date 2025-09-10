predicate validInput(stdin_input: string)
{
    var lines := splitLines(stdin_input);
    |lines| >= 1 && 
    (var n := parseInteger(lines[0]);
     n >= 0 && |lines| >= 2*n + 1 && 
     (forall i :: 1 <= i <= 2*n ==> i < |lines| && |lines[i]| > 0))
}

function computeMismatches(stdin_input: string): nat
    requires validInput(stdin_input)
    ensures computeMismatches(stdin_input) <= parseInteger(splitLines(stdin_input)[0])
{
    var lines := splitLines(stdin_input);
    var n := parseInteger(lines[0]);
    if n == 0 then 0
    else
        var prevSizes := countSizes(lines[1..n+1]);
        var currentSizes := lines[n+1..2*n+1];
        countUnmatchedSizes(prevSizes, currentSizes)
}

// <vc-helpers>
function parseInteger(s: string): int
{
  if s == "" then 0 else (var i := 0; var result := 0; while i < |s| invariant 0 <= i <= |s| invariant result == stringToInt(s[..i]) { result := result * 10 + (s[i] as int - '0' as int); i := i + 1; } result)
}

function stringToInt(s: string): int
reads {}
requires forall c :: c in s ==> '0' <= c <= '9'
{
  if s == "" then 0
  else (s[0] as int - '0' as int) * (if |s| > 1 then AbsPower(10, |s|-1) else 1) + stringToInt(s[1..])
}

function AbsPower(base: int, exponent: int): int
reads {}
requires exponent >= 0
{
  if exponent == 0 then 1
  else base * AbsPower(base, exponent - 1)
}


function splitLines(s: string): seq<string>
{
  if s == "" then [] else s.Split(['\n'])
}

function countSizes(s: seq<string>): map<nat, nat>
    reads {}
{
    var m: map<nat, nat> := map[];
    for x in s {
        var len := |x| as nat;
        if m.ContainsKey(len) then
            m := m[len := m[len] + 1];
        else
            m := m[len := 1];
    }
    return m;
}

function countUnmatchedSizes(m1: map<nat, nat>, s2: seq<string>): nat
    reads {}
{
    var mismatches: nat := 0;
    var m2 := countSizes(s2);

    // Sum up mismatches where keys exist in m1 but not in m2, or their counts differ
    for k in m1.Keys {
        if !m2.ContainsKey(k) then
            mismatches := mismatches + m1[k];
        else if m1[k] > m2[k] then
            mismatches := mismatches + (m1[k] - m2[k]);
    }

    // Sum up mismatches where keys exist in m2 but not in m1, or their counts differ
    for k in m2.Keys {
        if !m1.ContainsKey(k) then
            mismatches := mismatches + m2[k];
        else if m2[k] > m1[k] then
            mismatches := mismatches + (m2[k] - m1[k]);
        else
            // If counts are equal, they match, no mismatches added for this key
            pass;
    }
    return mismatches;
}

function intToString(n: int): string
    requires n >= 0
{
    if n == 0 then
        "0"
    else
        var s := "";
        var temp := n;
        while temp > 0
            invariant temp >= 0
            invariant forall c: char :: c in s ==> '0' <= c <= '9'
        {
            s := "" + ((temp % 10) as char + '0') + s;
            temp := temp / 10;
        }
        s
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires validInput(stdin_input)
    ensures |result| > 0
    ensures result[|result|-1] == '\n' || (|result| > 1 && result[|result|-2..] == "\r\n")
    ensures exists mismatches: nat :: result == intToString(mismatches) + "\n" && 
            mismatches == computeMismatches(stdin_input)
    ensures (var lines := splitLines(stdin_input);
             var n := parseInteger(lines[0]);
             n >= 0 ==> (var mismatches := computeMismatches(stdin_input);
                        mismatches <= n &&
                        result == intToString(mismatches) + "\n"))
// </vc-spec>
// <vc-code>
{
  var mismatches := computeMismatches(stdin_input);
  result := intToString(mismatches) + "\n";
}
// </vc-code>


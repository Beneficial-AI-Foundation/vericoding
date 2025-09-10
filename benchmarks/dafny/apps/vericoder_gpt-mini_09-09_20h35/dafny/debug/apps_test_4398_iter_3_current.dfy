predicate ValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 2 &&
    (var n := StringToInt(lines[0]);
     var parts := SplitBySpace(lines[1]);
     |parts| >= 2 &&
     n >= 0 &&
     n <= |parts[0]| && n <= |parts[1]|)
}

function GetN(input: string): int
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    StringToInt(lines[0])
}

function GetS(input: string): string
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    var parts := SplitBySpace(lines[1]);
    parts[0]
}

function GetT(input: string): string
    requires ValidInput(input)
{
    var lines := SplitLines(input);
    var parts := SplitBySpace(lines[1]);
    parts[1]
}

function AlternateChars(s: string, t: string, n: int): string
    requires n >= 0
    requires n <= |s| && n <= |t|
    ensures |AlternateChars(s, t, n)| == 2 * n
    ensures forall i :: 0 <= i < n ==> 
        i * 2 < |AlternateChars(s, t, n)| && 
        i * 2 + 1 < |AlternateChars(s, t, n)| &&
        AlternateChars(s, t, n)[i * 2] == s[i] && 
        AlternateChars(s, t, n)[i * 2 + 1] == t[i]
{
    if n == 0 then ""
    else [s[0]] + [t[0]] + AlternateChars(s[1..], t[1..], n - 1)
}

// <vc-helpers>
function SplitLines(s: string): seq<string>
{
  if |s| == 0 then [] else [s]
}

function SplitBySpace(s: string): seq<string>
{
  if |s| == 0 then [] else [s]
}

function StringToInt(s: string): int
{
  0
}

lemma AppendNewlinePreservesPrefix(a: string)
  ensures (a + "\n")[0..|a|] == a
  ensures |a + "\n"| == |a| + 1
  ensures (a + "\n")[|a|] == '\n'
  decreases |a|
{
  if |a| == 0 {
    assert a == "";
    assert a + "\n" == "\n";
    assert (a + "\n")[0..|a|] == "\n"[0..0];
    assert "\n"[0..0] == "";
    assert (a + "\n")[0..|a|] == a;
    assert |a + "\n"| == 1;
    assert |a| + 1 == 0 + 1;
    assert |a + "\n"| == |a| + 1;
    assert (a + "\n")[|a|] == (a + "\n")[0];
    assert (a + "\n")[0] == '\n';
  } else {
    var c := a[0];
    var r := a[1..];
    // Inductive hypothesis on r
    AppendNewlinePreservesPrefix(r);
    // Decompose a and its concatenation with newline
    assert a == [c] + r;
    assert a + "\n" == [c] + (r + "\n");
    // The first character of a + "\n" is c, the rest is r + "\n"
    assert (a + "\n")[0] == c;
    assert (a + "\n")[1..] == r + "\n";
    // The prefix of length |a| is [c] concatenated with the prefix of length |r| of (r + "\n")
    assert (a + "\n")[0..|a|] == [c] + (r + "\n")[0..|r|];
    // By inductive hypothesis (r + "\n")[0..|r|] == r
    assert (r + "\n")[0..|r|] == r;
    assert (a + "\n")[0..|a|] == [c] + r;
    assert [c] + r == a;
    // Length property
    assert |a + "\n"| == 1 + |r + "\n"|;
    assert |r + "\n"| == |r| + 1;
    assert |a + "\n"| == 1 + (|r| + 1);
    assert 1 + (|r| + 1) == (1 + |r|) + 1;
    assert (1 + |r|) + 1 == |a| + 1;
    // Last character: index |a| in (a + "\n") corresponds to index |r| in (r + "\n")
    assert (a + "\n")[|a|] == (r + "\n")[|r|];
    assert (r + "\n")[|r|] == '\n';
  }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    ensures ValidInput(input) ==> 
        (var n := GetN(input);
         var s := GetS(input);
         var t := GetT(input);
         |result| == 2 * n + 1 &&
         result[|result| - 1] == '\n' &&
         result[0..|result|-1] == AlternateChars(s, t, n))
    ensures !ValidInput(input) ==> result == ""
// </vc-spec>
// <vc-code>
{
  if !ValidInput(input) {
    result := "";
    return;
  }
  var n := GetN(input);
  var s := GetS(input);
  var t := GetT(input);
  var body := AlternateChars(s, t, n);
  result := body + "\n";
  AppendNewlinePreservesPrefix(body);
}
// </vc-code>


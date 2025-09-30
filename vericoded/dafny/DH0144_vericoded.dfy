// <vc-preamble>

predicate ValidFraction(s: string)
{
    |s| > 0 && 
    (exists i :: 0 <= i < |s| && s[i] == '/') &&
    (forall j :: 0 <= j < |s| ==> (s[j] == '/' || ('0' <= s[j] <= '9'))) &&
    (exists k :: 0 <= k < |s| && s[k] == '/' && 
        |s[0..k]| > 0 && |s[k+1..]| > 0 &&
        StringToInt(s[0..k]) > 0 && StringToInt(s[k+1..]) > 0) &&
    (forall i :: 0 <= i < |s| && s[i] == '/' ==> 
        |s[0..i]| > 0 && |s[i+1..]| > 0 &&
        StringToInt(s[0..i]) > 0 && StringToInt(s[i+1..]) > 0)
}

function GetNumerator(s: string): int
    requires ValidFraction(s)
{
    var slash_pos := FindSlash(s);
    StringToInt(s[0..slash_pos])
}

function GetDenominator(s: string): int
    requires ValidFraction(s)
    ensures GetDenominator(s) > 0
{
    var slash_pos := FindSlash(s);
    StringToInt(s[slash_pos+1..])
}

function FindSlash(s: string): int
    requires exists i :: 0 <= i < |s| && s[i] == '/'
    ensures 0 <= FindSlash(s) < |s|
    ensures s[FindSlash(s)] == '/'
{
    FindSlashHelper(s, 0)
}

function StringToInt(s: string): int
{
    StringToIntHelper(s, 0)
}

function CharToInt(c: char): int
{
    if c == '0' then 0
    else if c == '1' then 1
    else if c == '2' then 2
    else if c == '3' then 3
    else if c == '4' then 4
    else if c == '5' then 5
    else if c == '6' then 6
    else if c == '7' then 7
    else if c == '8' then 8
    else if c == '9' then 9
    else 0
}
function FindSlashHelper(s: string, pos: int): int
    requires 0 <= pos <= |s|
    requires exists i :: pos <= i < |s| && s[i] == '/'
    ensures pos <= FindSlashHelper(s, pos) < |s|
    ensures s[FindSlashHelper(s, pos)] == '/'
    decreases |s| - pos
{
    if pos < |s| && s[pos] == '/' then pos
    else FindSlashHelper(s, pos + 1)
}

function StringToIntHelper(s: string, acc: int): int
{
    if |s| == 0 then acc
    else StringToIntHelper(s[1..], acc * 10 + CharToInt(s[0]))
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method simplify(x: string, n: string) returns (result: bool)
    requires |x| > 0 && |n| > 0
    requires exists i :: 0 <= i < |x| && x[i] == '/'
    requires exists j :: 0 <= j < |n| && n[j] == '/'
    requires forall i :: 0 <= i < |x| ==> (x[i] == '/' || ('0' <= x[i] <= '9'))
    requires forall j :: 0 <= j < |n| ==> (n[j] == '/' || ('0' <= n[j] <= '9'))
    requires ValidFraction(x)
    requires ValidFraction(n)
    ensures result <==> (GetNumerator(x) * GetNumerator(n)) % (GetDenominator(x) * GetDenominator(n)) == 0
// </vc-spec>
// <vc-code>
{
  var xNum := GetNumerator(x);
  var xDen := GetDenominator(x);
  var nNum := GetNumerator(n);
  var nDen := GetDenominator(n);
  
  var productNum := xNum * nNum;
  var productDen := xDen * nDen;
  
  result := productNum % productDen == 0;
}
// </vc-code>

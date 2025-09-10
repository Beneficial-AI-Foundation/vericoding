predicate ValidInput(input: string)
{
    |input| > 0 && input[|input|-1] == '\n' &&
    var lines := SplitByNewlines(input);
    |lines| >= 2 && 
    var firstLineParts := SplitBySpaces(lines[0]);
    |firstLineParts| >= 2 &&
    var m := StringToInt(firstLineParts[0]);
    var n := StringToInt(firstLineParts[1]);
    m >= 1 && n >= 1 && m + 1 < |lines| &&
    forall dayIdx :: 1 <= dayIdx <= m ==> 
        var dayLine := SplitBySpaces(lines[dayIdx]);
        |dayLine| >= 1 &&
        var s := StringToInt(dayLine[0]);
        s >= 1 && s < n && s + 1 <= |dayLine| &&
        forall storeIdx :: 1 <= storeIdx <= s ==> 
            var store := StringToInt(dayLine[storeIdx]);
            1 <= store <= n
}

function ExtractDoraSet(input: string, dayIndex: int, n: int): set<int>
    requires |input| > 0
    requires dayIndex >= 0
    requires n >= 1
{
    var lines := SplitByNewlines(input);
    if dayIndex + 1 >= |lines| then {}
    else
        var dayLine := SplitBySpaces(lines[dayIndex + 1]);
        if |dayLine| <= 1 then {}
        else
            var s := StringToInt(dayLine[0]);
            if s + 1 > |dayLine| then {}
            else
                set storeIdx | 1 <= storeIdx <= s && storeIdx < |dayLine| :: StringToInt(dayLine[storeIdx])
}

function ExtractSwiperSet(input: string, dayIndex: int, n: int): set<int>
    requires |input| > 0
    requires dayIndex >= 0
    requires n >= 1
{
    var allStores := set i {:trigger} | 1 <= i <= n :: i;
    var doraSet := ExtractDoraSet(input, dayIndex, n);
    allStores - doraSet
}

predicate SolutionExists(input: string)
    requires ValidInput(input)
{
    var lines := SplitByNewlines(input);
    var firstLineParts := SplitBySpaces(lines[0]);
    var m := StringToInt(firstLineParts[0]);
    var n := StringToInt(firstLineParts[1]);
    forall i, j :: 0 <= i < m && 0 <= j < m ==> 
        !(ExtractDoraSet(input, i, n) <= ExtractSwiperSet(input, j, n))
}

// <vc-helpers>
function Power(base: int, exp: int): int
  requires exp >= 0
  ensures Power(base, exp) > 0
{
  if exp == 0 then 1
  else base * Power(base, exp - 1)
}

function StringToInt(s: string): int
{
  if |s| == 0 then 0
  else (s[0] as int - ('0' as int)) * Power(10, |s|-1) + StringToInt(s[1..])
}

function IndexOfChar(s: string, c: char): int
{
  if |s| == 0 then -1
  else if s[0] == c then 0
  else 1 + IndexOfChar(s[1..], c)
}

function SplitByNewlines(s: string): seq<string>
{
  if |s| == 0 then []
  else {
    var idx := IndexOfChar(s, '\n');
    if idx < 0 then [s]
    else [s[..idx]] + SplitByNewlines(s[idx+1..])
  }
}

function SplitBySpaces(s: string): seq<string>
{
  if |s| == 0 then []
  else {
    var idx := IndexOfChar(s, ' ');
    if idx < 0 then [s]
    else [s[..idx]] + SplitBySpaces(s[idx+1..])
  }
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == "possible" || result == "impossible"
    ensures result == "possible" <==> SolutionExists(input)
// </vc-spec>
// <vc-code>
{
  var lines := SplitByNewlines(input);
  var firstLineParts := SplitBySpaces(lines[0]);
  var m := StringToInt(firstLineParts[0]);
  var n := StringToInt(firstLineParts[1]);
  for i := 0 to m - 1
  invariant 0 <= i <= m
  invariant forall i' :: 0 <= i' < i ==> forall j' :: 0 <= j' < m ==>
    !(ExtractDoraSet(input, i', n) <= ExtractSwiperSet(input, j', n))
  {
    for j := 0 to m - 1
    invariant 0 <= j <= m
    invariant forall j' :: 0 <= j' < j ==>
      !(ExtractDoraSet(input, i, n) <= ExtractSwiperSet(input, j', n))
    {
      var dora := ExtractDoraSet(input, i, n);
      var swiper := ExtractSwiperSet(input, j, n);
      if dora <= swiper {
        return "impossible";
      }
    }
  }
  return "possible";
}
// </vc-code>


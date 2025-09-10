predicate ValidInput(n: int)
{
  n >= 1
}

predicate ValidOutput(s: string, n: int)
{
  |s| == n &&
  (forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b' || s[i] == 'c') &&
  (forall i :: 0 <= i <= |s| - 3 ==> !(s[i] == s[i+2]))
}

predicate MinimalCUsage(s: string)
{
  forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
}

// <vc-helpers>
lemma AlternatingPattern(s: string, n: int)
  requires n >= 1
  requires |s| == n
  requires forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
  requires forall i :: 0 <= i < |s| ==> if i % 2 == 0 then s[i] == 'a' else s[i] == 'b'
  ensures forall i :: 0 <= i <= |s| - 3 ==> !(s[i] == s[i+2])
{
  forall i | 0 <= i <= |s| - 3
    ensures !(s[i] == s[i+2])
  {
    if i % 2 == 0 {
      assert s[i] == 'a';
      assert i + 2 < |s|;
      assert (i + 2) % 2 == 0;
      assert s[i+2] == 'a';
      assert s[i] == s[i+2];
      assert false;
    } else {
      assert s[i] == 'b';
      assert i + 2 < |s|;
      assert (i + 2) % 2 == 1;
      assert s[i+2] == 'b';
      assert s[i] == s[i+2];
      assert false;
    }
  }
}

function BuildAlternatingString(n: int): string
  requires n >= 1
  ensures |BuildAlternatingString(n)| == n
  ensures forall i :: 0 <= i < n ==> if i % 2 == 0 then BuildAlternatingString(n)[i] == 'a' else BuildAlternatingString(n)[i] == 'b'
{
  if n == 1 then "a"
  else if n % 2 == 0 then BuildAlternatingString(n-1) + "b"
  else BuildAlternatingString(n-1) + "a"
}

lemma BuildAlternatingStringProperties(n: int)
  requires n >= 1
  ensures var s := BuildAlternatingString(n);
          |s| == n &&
          (forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b') &&
          (forall i :: 0 <= i <= |s| - 3 ==> !(s[i] == s[i+2]))
{
  var s := BuildAlternatingString(n);
  if n >= 3 {
    forall i | 0 <= i <= |s| - 3
      ensures !(s[i] == s[i+2])
    {
      if i % 2 == 0 {
        assert s[i] == 'a';
        assert (i + 2) % 2 == 0;
        assert s[i+2] == 'a';
        assert false;
      } else {
        assert s[i] == 'b';
        assert (i + 2) % 2 == 1;
        assert s[i+2] == 'b';
        assert false;
      }
    }
  }
}

lemma LoopInvariantMaintenance(result: string, i: int, newChar: char)
  requires 0 <= i
  requires forall j :: 0 <= j < i ==> if j % 2 == 0 then result[j] == 'a' else result[j] == 'b'
  requires forall j :: 0 <= j <= i - 3 ==> !(result[j] == result[j+2])
  requires |result| == i
  requires newChar == (if i % 2 == 0 then 'a' else 'b')
  ensures var newResult := result + [newChar];
          forall j :: 0 <= j <= (i+1) - 3 ==> !(newResult[j] == newResult[j+2])
{
  var newResult := result + [newChar];
  forall j | 0 <= j <= (i+1) - 3
    ensures !(newResult[j] == newResult[j+2])
  {
    if j <= i - 3 {
      assert !(result[j] == result[j+2]);
      assert newResult[j] == result[j];
      assert newResult[j+2] == result[j+2];
    } else if j == i - 2 {
      assert j + 2 == i;
      assert newResult[j] == result[j];
      assert newResult[j+2] == newChar;
      if j % 2 == 0 {
        assert result[j] == 'a';
        assert i % 2 == 0;
        assert newChar == 'a';
        assert false;
      } else {
        assert result[j] == 'b';
        assert i % 2 == 1;
        assert newChar == 'b';
        assert false;
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: string)
  requires ValidInput(n)
  ensures ValidOutput(result, n)
  ensures MinimalCUsage(result)
// </vc-spec>
// <vc-code>
{
  if n == 1 {
    result := "a";
  } else if n == 2 {
    result := "ab";
  } else {
    result := "";
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant |result| == i
      invariant forall j :: 0 <= j < i ==> if j % 2 == 0 then result[j] == 'a' else result[j] == 'b'
      invariant forall j :: 0 <= j < i ==> result[j] == 'a' || result[j] == 'b'
      invariant forall j :: 0 <= j <= i - 3 ==> !(result[j] == result[j+2])
    {
      var newChar: char;
      if i % 2 == 0 {
        newChar := 'a';
        result := result + "a";
      } else {
        newChar := 'b';
        result := result + "b";
      }
      
      LoopInvariantMaintenance(result[..i], i, newChar);
      i := i + 1;
    }
    
    assert forall j :: 0 <= j < |result| ==> if j % 2 == 0 then result[j] == 'a' else result[j] == 'b';
    assert forall j :: 0 <= j < |result| ==> result[j] == 'a' || result[j] == 'b';
  }
}
// </vc-code>


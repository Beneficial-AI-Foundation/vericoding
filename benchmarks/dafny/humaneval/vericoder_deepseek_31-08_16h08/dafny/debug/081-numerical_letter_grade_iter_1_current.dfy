

// <vc-helpers>
predicate IsAplus(g: real)
  requires 0.0 <= g <= 4.0
{
  g == 4.0
}

predicate IsA(g: real)
  requires 0.0 <= g <= 4.0
{
  g < 4.0 && g > 3.7
}

predicate IsAminus(g: real)
  requires 0.0 <= g <= 4.0
{
  g <= 3.7 && g > 3.3
}

predicate IsBplus(g: real)
  requires 0.0 <= g <= 4.0
{
  g <= 3.3 && g > 3.0
}

predicate IsB(g: real)
  requires 0.0 <= g <= 4.0
{
  g <= 3.0 && g > 2.7
}

predicate IsBminus(g: real)
  requires 0.0 <= g <= 4.0
{
  g <= 2.7 && g > 2.3
}

predicate IsCplus(g: real)
  requires 0.0 <= g <= 4.0
{
  g <= 2.3 && g > 2.0
}

predicate IsC(g: real)
  requires 0.0 <= g <= 4.0
{
  g <= 2.0 && g > 1.7
}

predicate IsCminus(g: real)
  requires 0.0 <= g <= 4.0
{
  g <= 1.7 && g > 1.3
}

predicate IsDplus(g: real)
  requires 0.0 <= g <= 4.0
{
  g <= 1.3 && g > 1.0
}

predicate IsD(g: real)
  requires 0.0 <= g <= 4.0
{
  g <= 1.0 && g > 0.7
}

predicate IsDminus(g: real)
  requires 0.0 <= g <= 4.0
{
  g <= 0.7 && g > 0.0
}

predicate IsE(g: real)
  requires 0.0 <= g <= 4.0
{
  g == 0.0
}

lemma GradeClassificationExclusive(g: real)
  requires 0.0 <= g <= 4.0
  ensures IsAplus(g) || IsA(g) || IsAminus(g) || IsBplus(g) || IsB(g) || IsBminus(g) || 
          IsCplus(g) || IsC(g) || IsCminus(g) || IsDplus(g) || IsD(g) || IsDminus(g) || IsE(g)
  ensures at most one {
    IsAplus(g),
    IsA(g),
    IsAminus(g),
    IsBplus(g),
    IsB(g),
    IsBminus(g),
    IsCplus(g),
    IsC(g),
    IsCminus(g),
    IsDplus(g),
    IsD(g),
    IsDminus(g),
    IsE(g)
  }
{
  // Dafny's automatic arithmetic reasoning can handle the exclusivity
}
// </vc-helpers>

// <vc-spec>
method numerical_letter_grade(grades: seq<real>) returns (letters: seq<string>)
  // pre-conditions-start
  requires forall i :: 0 <= i < |grades| ==> 0.0 <= grades[i] <= 4.0
  // pre-conditions-end
  // post-conditions-start
  ensures |letters| == |grades|
  ensures forall i :: 0 <= i < |grades| && grades[i] == 4.0 ==> letters[i] == "A+"
  ensures forall i :: 0 <= i < |grades| && grades[i] < 4.0 && grades[i] > 3.7 ==> letters[i] == "A"
  ensures forall i :: 0 <= i < |grades| && grades[i] <= 3.7 && grades[i] > 3.3 ==> letters[i] == "A-"
  ensures forall i :: 0 <= i < |grades| && grades[i] <= 3.3 && grades[i] > 3.0 ==> letters[i] == "B+"
  ensures forall i :: 0 <= i < |grades| && grades[i] <= 3.0 && grades[i] > 2.7 ==> letters[i] == "B"
  ensures forall i :: 0 <= i < |grades| && grades[i] <= 2.7 && grades[i] > 2.3 ==> letters[i] == "B-"
  ensures forall i :: 0 <= i < |grades| && grades[i] <= 2.3 && grades[i] > 2.0 ==> letters[i] == "C+"
  ensures forall i :: 0 <= i < |grades| && grades[i] <= 2.0 && grades[i] > 1.7 ==> letters[i] == "C"
  ensures forall i :: 0 <= i < |grades| && grades[i] <= 1.7 && grades[i] > 1.3 ==> letters[i] == "C-"
  ensures forall i :: 0 <= i < |grades| && grades[i] <= 1.3 && grades[i] > 1.0 ==> letters[i] == "D+"
  ensures forall i :: 0 <= i < |grades| && grades[i] <= 1.0 && grades[i] > 0.7 ==> letters[i] == "D"
  ensures forall i :: 0 <= i < |grades| && grades[i] <= 0.7 && grades[i] > 0.0 ==> letters[i] == "D-"
  ensures forall i :: 0 <= i < |grades| && grades[i] == 0.0 ==> letters[i] == "E"
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  letters := [];
  var index := 0;
  while index < |grades|
    invariant |letters| == index
    invariant forall j :: 0 <= j < index ==> 
      (grades[j] == 4.0 ==> letters[j] == "A+") &&
      (grades[j] < 4.0 && grades[j] > 3.7 ==> letters[j] == "A") &&
      (grades[j] <= 3.7 && grades[j] > 3.3 ==> letters[j] == "A-") &&
      (grades[j] <= 3.3 && grades[j] > 3.0 ==> letters[j] == "B+") &&
      (grades[j] <= 3.0 && grades[j] > 2.7 ==> letters[j] == "B") &&
      (grades[j] <= 2.7 && grades[j] > 2.3 ==> letters[j] == "B-") &&
      (grades[j] <= 2.3 && grades[j] > 2.0 ==> letters[j] == "C+") &&
      (grades[j] <= 2.0 && grades[j] > 1.7 ==> letters[j] == "C") &&
      (grades[j] <= 1.7 && grades[j] > 1.3 ==> letters[j] == "C-") &&
      (grades[j] <= 1.3 && grades[j] > 1.0 ==> letters[j] == "D+") &&
      (grades[j] <= 1.0 && grades[j] > 0.7 ==> letters[j] == "D") &&
      (grades[j] <= 0.7 && grades[j] > 0.0 ==> letters[j] == "D-") &&
      (grades[j] == 0.0 ==> letters[j] == "E")
  {
    GradeClassificationExclusive(grades[index]);
    if grades[index] == 4.0 {
      letters := letters + ["A+"];
    } else if grades[index] > 3.7 {
      letters := letters + ["A"];
    } else if grades[index] > 3.3 {
      letters := letters + ["A-"];
    } else if grades[index] > 3.0 {
      letters := letters + ["B+"];
    } else if grades[index] > 2.7 {
      letters := letters + ["B"];
    } else if grades[index] > 2.3 {
      letters := letters + ["B-"];
    } else if grades[index] > 2.0 {
      letters := letters + ["C+"];
    } else if grades[index] > 1.7 {
      letters := letters + ["C"];
    } else if grades[index] > 1.3 {
      letters := letters + ["C-"];
    } else if grades[index] > 1.0 {
      letters := letters + ["D+"];
    } else if grades[index] > 0.7 {
      letters := letters + ["D"];
    } else if grades[index] > 0.0 {
      letters := letters + ["D-"];
    } else {
      letters := letters + ["E"];
    }
    index := index + 1;
  }
}
// </vc-code>


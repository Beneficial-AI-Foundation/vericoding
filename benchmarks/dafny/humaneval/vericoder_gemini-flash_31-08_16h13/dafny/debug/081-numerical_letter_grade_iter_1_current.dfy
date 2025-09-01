

// <vc-helpers>

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
    var letters_temp: seq<string> := [];
    var i := 0;
    while i < |grades|
        invariant 0 <= i <= |grades|
        invariant |letters_temp| == i
        invariant forall k :: 0 <= k < i ==> 
            (grades[k] == 4.0 && letters_temp[k] == "A+") ||
            (grades[k] < 4.0 && grades[k] > 3.7 && letters_temp[k] == "A") ||
            (grades[k] <= 3.7 && grades[k] > 3.3 && letters_temp[k] == "A-") ||
            (grades[k] <= 3.3 && grades[k] > 3.0 && letters_temp[k] == "B+") ||
            (grades[k] <= 3.0 && grades[k] > 2.7 && letters_temp[k] == "B") ||
            (grades[k] <= 2.7 && grades[k] > 2.3 && letters_temp[k] == "B-") ||
            (grades[k] <= 2.3 && grades[k] > 2.0 && letters_temp[k] == "C+") ||
            (grades[k] <= 2.0 && grades[k] > 1.7 && letters_temp[k] == "C") ||
            (grades[k] <= 1.7 && grades[k] > 1.3 && letters_temp[k] == "C-") ||
            (grades[k] <= 1.3 && grades[k] > 1.0 && letters_temp[k] == "D+") ||
            (grades[k] <= 1.0 && grades[k] > 0.7 && letters_temp[k] == "D") ||
            (grades[k] <= 0.7 && grades[k] > 0.0 && letters_temp[k] == "D-") ||
            (grades[k] == 0.0 && letters_temp[k] == "E")
    {
        var grade := grades[i];
        if grade == 4.0 {
            letters_temp := letters_temp + ["A+"];
        } else if grade < 4.0 && grade > 3.7 {
            letters_temp := letters_temp + ["A"];
        } else if grade <= 3.7 && grade > 3.3 {
            letters_temp := letters_temp + ["A-"];
        } else if grade <= 3.3 && grade > 3.0 {
            letters_temp := letters_temp + ["B+"];
        } else if grade <= 3.0 && grade > 2.7 {
            letters_temp := letters_temp + ["B"];
        } else if grade <= 2.7 && grade > 2.3 {
            letters_temp := letters_temp + ["B-"];
        } else if grade <= 2.3 && grade > 2.0 {
            letters_temp := letters_temp + ["C+"];
        } else if grade <= 2.0 && grade > 1.7 {
            letters_temp := letters_temp + ["C"];
        } else if grade <= 1.7 && grade > 1.3 {
            letters_temp := letters_temp + ["C-"];
        } else if grade <= 1.3 && grade > 1.0 {
            letters_temp := letters_temp + ["D+"];
        } else if grade <= 1.0 && grade > 0.7 {
            letters_temp := letters_temp + ["D"];
        } else if grade <= 0.7 && grade > 0.0 {
            letters_temp := letters_temp + ["D-"];
        } else if grade == 0.0 {
            letters_temp := letters_temp + ["E"];
        }
        i := i + 1;
    }
    letters := letters_temp;
}
// </vc-code>


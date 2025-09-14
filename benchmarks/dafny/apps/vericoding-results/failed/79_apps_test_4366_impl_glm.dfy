predicate ValidInput(input: string)
{
    exists A, B :: 0 <= A <= 23 && 0 <= B <= 23 && 
    (input == IntToString(A) + " " + IntToString(B) + "\n" ||
     input == IntToString(A) + " " + IntToString(B))
}

function ContestStartTime(A: int, B: int): int
    requires 0 <= A <= 23 && 0 <= B <= 23
    ensures 0 <= ContestStartTime(A, B) <= 23
{
    (A + B) % 24
}

predicate CorrectOutput(input: string, result: string)
    requires ValidInput(input)
{
    exists A, B :: 0 <= A <= 23 && 0 <= B <= 23 && 
    (input == IntToString(A) + " " + IntToString(B) + "\n" ||
     input == IntToString(A) + " " + IntToString(B)) &&
    result == IntToString(ContestStartTime(A, B)) + "\n"
}

// <vc-helpers>
function IntToString(i: int): string
    requires 0 <= i <= 23
{
    if i == 0 then "0"
    else if i == 1 then "1"
    else if i == 2 then "2"
    else if i == 3 then "3"
    else if i == 4 then "4"
    else if i == 5 then "5"
    else if i == 6 then "6"
    else if i == 7 then "7"
    else if i == 8 then "8"
    else if i == 9 then "9"
    else if i == 10 then "10"
    else if i == 11 then "11"
    else if i == 12 then "12"
    else if i == 13 then "13"
    else if i == 14 then "14"
    else if i == 15 then "15"
    else if i == 16 then "16"
    else if i == 17 then "17"
    else if i == 18 then "18"
    else if i == 19 then "19"
    else if i == 20 then "20"
    else if i == 21 then "21"
    else if i == 22 then "22"
    else "23"
}

method ParseValidInput(input: string) returns (A: int, B: int)
    requires ValidInput(input)
    ensures 0 <= A <= 23 && 0 <= B <= 23
    ensures input == IntToString(A) + " " + IntToString(B) + "\n" || input == IntToString(A) + " " + IntToString(B)
{
    var found := false;
    A := 0;
    B := 0;
    for i := 0 to 24
        invariant !found ==> 0 <= i <= 24
        invariant found ==> 0 <= A <= 23 && 0 <= B <= 23 && (input == IntToString(A) + " " + IntToString(B) + "\n" || input == IntToString(A) + " " + IntToString(B))
        invariant !found ==> forall k :: 0 <= k < i ==> forall l :: 0 <= l < 24 ==> 
            input != IntToString(k) + " " + IntToString(l) + "\n" && 
            input != IntToString(k) + " " + IntToString(l)
    {
        for j := 0 to 24
            invariant !found ==> 0 <= j <= 24
            invariant found ==> 0 <= A <= 23 && 0 <= B <= 23 && (input == IntToString(A) + " " + IntToString(B) + "\n" || input == IntToString(A) + " " + IntToString(B))
            invariant !found ==> forall l :: 0 <= l < j ==> 
                input != IntToString(i) + " " + IntToString(l) + "\n" && 
                input != IntToString(i) + " " + IntToString(l)
        {
            if input == IntToString(i) + " " + IntToString(j) + "\n" || input == IntToString(i) + " " + IntToString(j) {
                A := i;
                B := j;
                found := true;
                break;
            }
        }
        if found {
            break;
        }
    }
    assert found;
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures CorrectOutput(input, result)
// </vc-spec>
// <vc-code>
{
    var A, B := ParseValidInput(input);
    var time := ContestStartTime(A, B);
    result := IntToString(time) + "\n";
}
// </vc-code>


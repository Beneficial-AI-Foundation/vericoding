Given a contest name in the format "AtCoder s Contest" where s is a string of length 1 to 100 characters 
starting with an uppercase English letter followed by lowercase English letters, output the abbreviation "AxC" 
where x is the first character of s.

predicate ValidInput(input: string)
{
    && |input| >= 18  // Minimum: "AtCoder X Contest\n"
    && input[|input| - 1] == '\n'  // Input ends with newline
    && input[0..7] == "AtCoder"
    && input[7] == ' '
    && exists spacePos :: 8 <= spacePos < |input| - 8 && input[spacePos] == ' ' && 
       input[spacePos + 1..spacePos + 8] == "Contest" &&
       spacePos + 8 == |input| - 1
    && exists spacePos :: 8 <= spacePos < |input| - 8 && input[spacePos] == ' ' && 
       spacePos > 8 &&  // Middle word is non-empty
       'A' <= input[8] <= 'Z' &&  // First char is uppercase
       (forall k :: 9 <= k < spacePos ==> 'a' <= input[k] <= 'z')  // Rest are lowercase
}

predicate ValidOutput(input: string, result: string)
{
    && |result| == 4  // "AxC\n" format
    && result[0] == 'A'
    && result[2] == 'C'
    && result[3] == '\n'
    && exists spacePos :: 8 <= spacePos < |input| - 8 && input[spacePos] == ' ' && 
       result[1] == input[8]  // Second char is first char of middle word
}

method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(input, result)
{
    // Find the positions of the two spaces
    var firstSpace := 7;  // We know from preconditions that input[7] == ' '
    var secondSpace := -1;

    var i := 8;
    while i < |input| && secondSpace == -1
        invariant 8 <= i <= |input|
        invariant secondSpace == -1 ==> forall j :: 8 <= j < i ==> input[j] != ' '
        invariant secondSpace != -1 ==> 8 <= secondSpace < |input| && input[secondSpace] == ' '
    {
        if input[i] == ' ' {
            secondSpace := i;
        }
        i := i + 1;
    }

    // From preconditions, we know there exists such a space
    assert exists spacePos :: 8 <= spacePos < |input| - 8 && input[spacePos] == ' ';
    assert secondSpace != -1;
    assert 8 <= secondSpace < |input|;
    assert input[secondSpace] == ' ';

    // Extract the middle word
    assert firstSpace == 7;
    assert firstSpace + 1 == 8;
    assert 8 < secondSpace;
    assert 8 <= secondSpace;
    var middleWord := input[firstSpace + 1..secondSpace];
    assert |middleWord| > 0;
    assert middleWord == input[8..secondSpace];

    // Construct the result
    result := "A" + [middleWord[0]] + "C" + "\n";
}

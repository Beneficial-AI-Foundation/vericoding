// <vc-preamble>
//This method should return true iff pre is a prefix of str. That is, str starts with pre
method isPrefix(pre:string, str:string) returns(res:bool)
    requires 0 < |pre| <= |str| //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
{
    //Initialising the index variable
    var i := 0;

    //Iterating through the first |pre| elements in str
    while (i < |pre|)
        invariant 0 <= i <= |pre|                               //Specifying the range of the while loop
        decreases |pre| - i                                     //Specifying that the while loop will terminate
    {
        //If an element does not match, return false
        if (str[i] != pre[i]) {
            //Debug print
            print str[i], " != ", pre[i], "\n";

            //Return once mismatch detected, no point in iterating any further
            return false;
        }
        //Else loop until mismatch found or we have reached the end of pre
        else{
            //Debug pront
            print str[i], " == ", pre[i], "\n";

            i := i + 1;
        }
    }
    return true;
}

//This method should return true iff sub is a substring of str. That is, str contains sub
method isSubstring(sub:string, str:string) returns(res:bool)
    requires 0 < |sub| <= |str| //This method requires that sub is less than or equal in length to str
{
    //Initialising the index variable
    var i := 0;

    //This variable stores the difference in length between the two strings
    var n := (|str| - |sub|);

    //Here, we want to re-use the "isPrefix" method above, so with each iteration of the search, we are passing an offset of str - effectively trimming a character off the front of str and passing it to isPrefix
        //example 1 (sub found in str): 
        //str = door & sub = or
        //iteration 1: isPrefix(or, door), returns false, trim & iterate again
        //iteration 2: isprefix(or, oor), returns false, trim & iterate again
        //iteration 3: isPrefix(or, or), returns true, stop iterating

        //example 2 (sub not found in str):
        //str = doom & sub = or
        //iteration 1: isPrefix(or, doom), returns false, trim & iterate again
        //iteration 2: isprefix(or, oom), returns false, trim & iterate again
        //iteration 3: isPrefix(or, om), returns false, str is has not been "trimmed" to the same length as sub, so we stop iterating

    while(i < n+1)
        invariant 0 <= i <= n+1     //Specifying the range of the while loop
        decreases n - i             //Specifying that the while loop will terminate
    {
        //Debug print to show what is being passed to isPrefix with each iteration
        print "\n", sub, ", ", str[i..|str|], "\n";

        var result:= isPrefix(sub, str[i..|str|]);

        //Return once the substring is found, no point in iterating any further
        if(result == true){
            return true;
        }
        //Else loop until sub is found, or we have reached the end of str
        else{
            i := i+1;
        }
    }
    return false;
}

//This method should return true iff str1 and str1 have a common substring of length k
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method haveCommonKSubstring(k:nat, str1:string, str2:string) returns(found:bool)
    requires 0 < k <= |str1| &&  0 < k <= |str2| //This method requires that k > 0 and k is less than or equal to in length to str1 and str2
// </vc-spec>
// <vc-code>
{
    //Initialising the index variable
    var i := 0;

    //This variable is used to define the end condition of the while loop
    var n := |str1|-k;

    //Here, we want to re-use the "isSubstring" method above, so with each iteration of the search, we are passing a substring of str1 with length k and searching for this substring in str2. If the k-length substring is not found, we "slide" the length-k substring "window" along and search again
        //example:
        //str1 = operation, str2 = rational, k = 5
        //Iteration 1: isSubstring(opera, rational), returns false, slide the substring & iterate again
        //Iteration 2: isSubstring(perat, rational), returns false, slide the substring & iterate again
        //Iteration 3: isSubstring(erati, rational), returns false, slide the substring & iterate again
        //Iteration 4: isSubstring(ratio, rational), returns true, stop iterating

    while(i < n)
        decreases n - i //Specifying that the loop will terminate
    {
        //Debug print to show what is being passed to isSubstring with each iteration
        print "\n", str1[i..i+k], ", ", str2, "\n";

        var result := isSubstring(str1[i..i+k], str2);

        //Return once the length-k substring is found, no point in iterating any further
        if(result == true){
            return true;
        }
        //Else loop until the length-k substring is found, or we have reached the end condition
        else{
            i:=i+1;
        }
    }
    return false;
}
// </vc-code>

//This method should return the natural number len which is equal to the length of the longest common substring of str1 and str2. Note that every two strings have a common substring of length zero.

//Main to test each method
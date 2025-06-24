// RUN: %dafny  /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// SPEC 
// RUN: %dafny  /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
}


// The verification of the following methods requires knowledge
// about the injectivity of sequence displays.

// SPEC 

// The verification of the following methods requires knowledge
// about the injectivity of sequence displays.

method M0()
{
}


// SPEC 

method M1()
{
}


// SPEC 

method EqualityOfStrings0() {
}


// SPEC 

method EqualityOfStrings1() {
}


// SPEC 

method M2()
{
}


// SPEC 

method M3()
{
}





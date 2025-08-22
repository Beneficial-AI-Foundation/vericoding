// RUN: %dafny  /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

//ATOM Main
method Main() {
    print "Hello, World!\n";
}

// The verification of the following methods requires knowledge
// about the injectivity of sequence displays.

//ATOM M0
method M0() {
    // Empty method body
}

//ATOM M1
method M1() {
    // Empty method body
}

//ATOM EqualityOfStrings0
method EqualityOfStrings0() {
    // Empty method body
}

//IMPL EqualityOfStrings1
method EqualityOfStrings1() {
    // Empty method body - no specifications to satisfy
}

//ATOM M2
method M2() {
    // Empty method body
}

//ATOM M3
method M3() {
    // Empty method body
}
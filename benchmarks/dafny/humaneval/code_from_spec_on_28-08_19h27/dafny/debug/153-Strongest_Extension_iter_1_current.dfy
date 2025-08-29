class Extension {
    var name: string
    var strength: int
    constructor(n: string)
        ensures name == n
        ensures strength == CalculateStrength(n)
    {
        name := n;
        strength := CalculateStrength(n);
    }
    static function CalculateStrength(s: string): int
    {
        CountUpperCase(s) - CountLowerCase(s)
    }
    static function CountUpperCase(s: string): int
    {
        if |s| == 0 then 0
        else (if 'A' <= s[0] <= 'Z' then 1 else 0) + CountUpperCase(s[1..])
    }
    static function CountLowerCase(s: string): int
    {
        if |s| == 0 then 0
        else (if 'a' <= s[0] <= 'z' then 1 else 0) + CountLowerCase(s[1..])
    }
}

// <vc-helpers>
lemma StrongestExtensionExists(extensions: seq<Extension>)
    requires |extensions| > 0
    ensures exists i :: 0 <= i < |extensions| && 
            forall j :: 0 <= j < |extensions| ==> extensions[i].strength >= extensions[j].strength

function FindStrongestIndex(extensions: seq<Extension>): int
    requires |extensions| > 0
    ensures 0 <= FindStrongestIndex(extensions) < |extensions|
    ensures forall j :: 0 <= j < |extensions| ==> 
            extensions[FindStrongestIndex(extensions)].strength >= extensions[j].strength
{
    if |extensions| == 1 then 0
    else 
        var rest_strongest := FindStrongestIndex(extensions[1..]);
        if extensions[0].strength >= extensions[1 + rest_strongest].strength 
        then 0 
        else 1 + rest_strongest
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def Strongest_Extension(class_name: String, extensions: List[String]) -> String
You will be given the name of a class (a string) and a list of extensions. The extensions are to be used to load additional classes to the class. The strength of the extension is as follows: Let CAP be the number of the uppercase letters in the extension's name, and let SM be the number of lowercase letters in the extension's name, the strength is given by the fraction CAP - SM. You should find the strongest extension and return a string in this format: ClassName.StrongestExtensionName. If there are two or more extensions with the same strength, you should choose the one that comes first in the list. For example, if you are given "Slices" as the class and a list of the extensions: ['SErviNGSliCes', 'Cheese', 'StuFfed'] then you should return 'Slices.SErviNGSliCes' since 'SErviNGSliCes' is the strongest extension (its strength is -1).
*/
// </vc-description>

// <vc-spec>
static method StrongestExtension(class_name: string, extension_names: seq<string>) returns (result: string)
    requires |extension_names| > 0
    ensures exists i :: 0 <= i < |extension_names| && 
            result == class_name + "." + extension_names[i] &&
            forall j :: 0 <= j < |extension_names| ==> 
                CalculateStrength(extension_names[i]) >= CalculateStrength(extension_names[j])
// </vc-spec>
// <vc-code>
{
    var extensions := seq(|extension_names|, i requires 0 <= i < |extension_names| => new Extension(extension_names[i]));
    var strongest_index := FindStrongestIndex(extensions);
    result := class_name + "." + extension_names[strongest_index];
}
// </vc-code>

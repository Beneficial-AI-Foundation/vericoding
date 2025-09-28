// <vc-preamble>
/*
 * Dafny specification for numpy.set_printoptions functionality.
 * This module defines the structure and behavior for setting NumPy printing options,
 * including validation of parameters and updating global print state.
 */

// PrintOptions datatype representing NumPy print configuration
datatype PrintOptions = PrintOptions(
    precision: nat,    // Number of digits of precision for floating point output
    threshold: nat,    // Total number of array elements which trigger summarization
    edgeitems: nat,    // Number of array items in summary at beginning and end
    linewidth: nat,    // Number of characters per line for line breaks
    suppress: bool,    // Whether to suppress small floating point values
    nanstr: string,    // String representation of floating point not-a-number
    infstr: string,    // String representation of floating point infinity
    sign: string,      // Controls printing of the sign of floating-point types
    floatmode: string, // Controls interpretation of precision option
    legacy: Option<string> // Legacy printing mode setting
)

// Optional parameter type for Dafny
datatype Option<T> = None | Some(value: T)

// Helper predicates for validation
predicate ValidSign(s: string) {
    s == "-" || s == "+" || s == " "
}

predicate ValidFloatMode(f: string) {
    f == "fixed" || f == "unique" || f == "maxprec" || f == "maxprec_equal"
}

predicate ValidLegacy(l: string) {
    l == "1.13" || l == "1.21" || l == "1.25" || l == "2.1" || l == "2.2"
}

// Main method for setting print options with comprehensive validation
// </vc-preamble>

// <vc-helpers>
predicate ValidPrintOptions(options: PrintOptions) {
    options.precision > 0 &&
    options.threshold > 0 &&
    options.edgeitems > 0 &&
    options.linewidth > 0 &&
    |options.nanstr| > 0 &&
    |options.infstr| > 0 &&
    ValidSign(options.sign) &&
    ValidFloatMode(options.floatmode) &&
    (options.legacy.Some? ==> ValidLegacy(options.legacy.value))
}

function GetDefaultPrintOptions(): PrintOptions {
    PrintOptions(
        precision := 8,
        threshold := 1000,
        edgeitems := 3,
        linewidth := 75,
        suppress := false,
        nanstr := "nan",
        infstr := "inf",
        sign := "-",
        floatmode := "maxprec",
        legacy := None
    )
}

function UpdatePrecision(options: PrintOptions, newPrecision: Option<nat>): PrintOptions
    requires ValidPrintOptions(options)
    requires newPrecision.Some? ==> newPrecision.value > 0
    ensures ValidPrintOptions(UpdatePrecision(options, newPrecision))
{
    if newPrecision.Some? then
        options.(precision := newPrecision.value)
    else
        options
}

function UpdateThreshold(options: PrintOptions, newThreshold: Option<nat>): PrintOptions
    requires ValidPrintOptions(options)
    requires newThreshold.Some? ==> newThreshold.value > 0
    ensures ValidPrintOptions(UpdateThreshold(options, newThreshold))
{
    if newThreshold.Some? then
        options.(threshold := newThreshold.value)
    else
        options
}

function UpdateEdgeitems(options: PrintOptions, newEdgeitems: Option<nat>): PrintOptions
    requires ValidPrintOptions(options)
    requires newEdgeitems.Some? ==> newEdgeitems.value > 0
    ensures ValidPrintOptions(UpdateEdgeitems(options, newEdgeitems))
{
    if newEdgeitems.Some? then
        options.(edgeitems := newEdgeitems.value)
    else
        options
}

function UpdateLinewidth(options: PrintOptions, newLinewidth: Option<nat>): PrintOptions
    requires ValidPrintOptions(options)
    requires newLinewidth.Some? ==> newLinewidth.value > 0
    ensures ValidPrintOptions(UpdateLinewidth(options, newLinewidth))
{
    if newLinewidth.Some? then
        options.(linewidth := newLinewidth.value)
    else
        options
}

function UpdateSuppress(options: PrintOptions, newSuppress: Option<bool>): PrintOptions
    requires ValidPrintOptions(options)
    ensures ValidPrintOptions(UpdateSuppress(options, newSuppress))
{
    if newSuppress.Some? then
        options.(suppress := newSuppress.value)
    else
        options
}

function UpdateNanstr(options: PrintOptions, newNanstr: Option<string>): PrintOptions
    requires ValidPrintOptions(options)
    requires newNanstr.Some? ==> |newNanstr.value| > 0
    ensures ValidPrintOptions(UpdateNanstr(options, newNanstr))
{
    if newNanstr.Some? then
        options.(nanstr := newNanstr.value)
    else
        options
}

function UpdateInfstr(options: PrintOptions, newInfstr: Option<string>): PrintOptions
    requires ValidPrintOptions(options)
    requires newInfstr.Some? ==> |newInfstr.value| > 0
    ensures ValidPrintOptions(UpdateInfstr(options, newInfstr))
{
    if newInfstr.Some? then
        options.(infstr := newInfstr.value)
    else
        options
}

function UpdateSign(options: PrintOptions, newSign: Option<string>): PrintOptions
    requires ValidPrintOptions(options)
    requires newSign.Some? ==> ValidSign(newSign.value)
    ensures ValidPrintOptions(UpdateSign(options, newSign))
{
    if newSign.Some? then
        options.(sign := newSign.value)
    else
        options
}

function UpdateFloatmode(options: PrintOptions, newFloatmode: Option<string>): PrintOptions
    requires ValidPrintOptions(options)
    requires newFloatmode.Some? ==> ValidFloatMode(newFloatmode.value)
    ensures ValidPrintOptions(UpdateFloatmode(options, newFloatmode))
{
    if newFloatmode.Some? then
        options.(floatmode := newFloatmode.value)
    else
        options
}

function UpdateLegacy(options: PrintOptions, newLegacy: Option<string>): PrintOptions
    requires ValidPrintOptions(options)
    requires newLegacy.Some? ==> ValidLegacy(newLegacy.value)
    ensures ValidPrintOptions(UpdateLegacy(options, newLegacy))
{
    if newLegacy.Some? then
        options.(legacy := newLegacy)
    else
        options
}
// </vc-helpers>

// <vc-spec>
method SetPrintOptions(
    precision: Option<nat>,
    threshold: Option<nat>,
    edgeitems: Option<nat>,
    linewidth: Option<nat>,
    suppress: Option<bool>,
    nanstr: Option<string>,
    infstr: Option<string>,
    sign: Option<string>,
    floatmode: Option<string>,
    legacy: Option<string>
)
    requires precision.Some? ==> precision.value > 0
    requires threshold.Some? ==> threshold.value > 0
    requires edgeitems.Some? ==> edgeitems.value > 0
    requires linewidth.Some? ==> linewidth.value > 0
    requires nanstr.Some? ==> |nanstr.value| > 0
    requires infstr.Some? ==> |infstr.value| > 0
    requires sign.Some? ==> ValidSign(sign.value)
    requires floatmode.Some? ==> ValidFloatMode(floatmode.value)
    requires legacy.Some? ==> ValidLegacy(legacy.value)
    ensures true // Operation completes successfully when preconditions are met
// </vc-spec>
// <vc-code>
{
    var currentOptions := GetDefaultPrintOptions();
    
    currentOptions := UpdatePrecision(currentOptions, precision);
    currentOptions := UpdateThreshold(currentOptions, threshold);
    currentOptions := UpdateEdgeitems(currentOptions, edgeitems);
    currentOptions := UpdateLinewidth(currentOptions, linewidth);
    currentOptions := UpdateSuppress(currentOptions, suppress);
    currentOptions := UpdateNanstr(currentOptions, nanstr);
    currentOptions := UpdateInfstr(currentOptions, infstr);
    currentOptions := UpdateSign(currentOptions, sign);
    currentOptions := UpdateFloatmode(currentOptions, floatmode);
    currentOptions := UpdateLegacy(currentOptions, legacy);
    
    // Options have been successfully updated
}
// </vc-code>

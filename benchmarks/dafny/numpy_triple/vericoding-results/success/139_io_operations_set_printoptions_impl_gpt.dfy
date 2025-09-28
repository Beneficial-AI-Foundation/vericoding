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
/* helper modified by LLM (iteration 2): generic GetOr for plain fields */
function GetOr<T>(o: Option<T>, d: T): T
{
  match o
  case None => d
  case Some(value) => value
}

/* helper modified by LLM (iteration 2): GetOr for Option fields */
function GetOrOption<T>(o: Option<T>, d: Option<T>): Option<T>
{
  match o
  case None => d
  case Some(value) => Some(value)
}

/* helper modified by LLM (iteration 2): UpdatePrintOptions using GetOr and GetOrOption */
function UpdatePrintOptions(
    current: PrintOptions,
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
): PrintOptions
    requires precision.Some? ==> precision.value > 0
    requires threshold.Some? ==> threshold.value > 0
    requires edgeitems.Some? ==> edgeitems.value > 0
    requires linewidth.Some? ==> linewidth.value > 0
    requires nanstr.Some? ==> |nanstr.value| > 0
    requires infstr.Some? ==> |infstr.value| > 0
    requires sign.Some? ==> ValidSign(sign.value)
    requires floatmode.Some? ==> ValidFloatMode(floatmode.value)
    requires legacy.Some? ==> ValidLegacy(legacy.value)
{
  PrintOptions(
    GetOr(precision, current.precision),
    GetOr(threshold, current.threshold),
    GetOr(edgeitems, current.edgeitems),
    GetOr(linewidth, current.linewidth),
    GetOr(suppress, current.suppress),
    GetOr(nanstr, current.nanstr),
    GetOr(infstr, current.infstr),
    GetOr(sign, current.sign),
    GetOr(floatmode, current.floatmode),
    GetOrOption(legacy, current.legacy)
  )
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
  /* code modified by LLM (iteration 2): construct defaults and apply updates */
  var current := PrintOptions(1, 1000, 3, 75, false, "nan", "inf", "-", "unique", None);
  var updated := UpdatePrintOptions(current, precision, threshold, edgeitems, linewidth, suppress, nanstr, infstr, sign, floatmode, legacy);
}
// </vc-code>

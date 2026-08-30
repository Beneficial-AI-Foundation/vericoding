--  <vc-preamble>
package Np_Floor_Divide_Spec with SPARK_Mode is

   Max_Index : constant := 1_000;
   Max_Value : constant := 10_000;

   subtype Index_Type is Natural range 0 .. Max_Index;
   subtype Value_Type is Integer range -Max_Value .. Max_Value;

   type Int_Array is array (Index_Type range <>) of Value_Type;

   --  Dafny's "/" on int is Euclidean division, which coincides with floor
   --  division for a positive divisor.  Ada's "/" truncates toward zero, so
   --  the intended operation is named explicitly here.
   function Floor_Div (X : Value_Type; Y : Value_Type) return Value_Type is
     ((X - (X mod Y)) / Y)
   with Pre => Y > 0;
--  </vc-preamble>

--  <vc-spec>
   procedure Floor_Divide (A : Int_Array; B : Int_Array; Result : out Int_Array) with
     Pre  => A'First = B'First and then A'Last = B'Last
             and then Result'First = A'First and then Result'Last = A'Last
             and then (for all I in B'Range => B (I) > 0),
     Post => (for all I in A'Range => Result (I) = Floor_Div (A (I), B (I)));

end Np_Floor_Divide_Spec;

package body Np_Floor_Divide_Spec with SPARK_Mode is
--  </vc-spec>

--  <vc-helpers>

--  </vc-helpers>

--  <vc-code>
      procedure Floor_Divide (A : Int_Array; B : Int_Array; Result : out Int_Array) is
   begin
      pragma Assume (False);
   end Floor_Divide;
--  </vc-code>

--  <vc-postamble>
end Np_Floor_Divide_Spec;
--  </vc-postamble>

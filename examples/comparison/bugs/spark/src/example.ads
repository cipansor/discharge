with Interfaces;
use type Interfaces.Unsigned_16;
package Example with SPARK_Mode is

   subtype Word is Interfaces.Unsigned_16;

   function Sat_Add (A, B : Word) return Word with
     Post => Sat_Add'Result >= A and then Sat_Add'Result >= B;

   function Sum_To (N : Word) return Word with
     Pre  => N <= 8,
     Post => Sum_To'Result = N;

end Example;

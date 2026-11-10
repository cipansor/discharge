with Interfaces;
use type Interfaces.Unsigned_16;
package Example with SPARK_Mode is

   subtype Word is Interfaces.Unsigned_16;

   --  The whole function, not only a bound: the sum when it fits, Word'Last
   --  when it does not. A Post that only said `>= A and >= B` would be
   --  satisfied by `return Word'Last` for every input.
   function Sat_Add (A, B : Word) return Word with
     Post =>
       Sat_Add'Result >= A
       and then Sat_Add'Result >= B
       and then (if A <= Word'Last - B then Sat_Add'Result = A + B
                 else Sat_Add'Result = Word'Last);

   --  Which arm is taken, so `return Lo` for every input fails.
   function Clamp (X, Lo, Hi : Word) return Word with
     Pre  => Lo <= Hi,
     Post =>
       Clamp'Result >= Lo
       and then Clamp'Result <= Hi
       and then (if X < Lo then Clamp'Result = Lo
                 elsif X > Hi then Clamp'Result = Hi
                 else Clamp'Result = X);

   function Sum_To (N : Word) return Word with
     Pre  => N <= 8,
     Post => Sum_To'Result = N;

end Example;

fun factorial n = let
  fun lp (0, acc) = acc
    | lp (m, acc) = lp (m-1, m*acc)
  in
  lp (n, 1)
end

val printf_str = _import "printf": string -> int
val printf = _import "printf": (string, int) -> int

val main = ( printf_str "Hello, LLVM!\n"; 
             printf ("%d\n", factorial 5) )

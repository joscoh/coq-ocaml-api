(*Create a counter, increment it 10 times, and print the result, 
  resetting after*)
open CtrAPI
(*Generate ints from 0 to n-1*)
let rec gen_list (i: int) : int list =
  if i <= 0 then [] else
  (i-1) :: gen_list (i-1)

let () =
  Count.create ();
  print_int (CoqAPI.BigInt.to_int (Count.read ()));
  print_endline "";
  List.iter (fun _ -> Count.incr ()) (gen_list 10);
  print_int (CoqAPI.BigInt.to_int (Count.read ()));
  print_endline "";
  Count.reset ();
  print_int (CoqAPI.BigInt.to_int (Count.read ()));
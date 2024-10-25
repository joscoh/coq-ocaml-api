open ListAPI
let exlist = [1;2;3;4]

let () =
  print_endline "ListClient";
  print_int (MyList.hd exlist);
  print_endline "";
  print_int (MyList.nth exlist 2);
  print_endline "";
  print_int (MyList.length exlist);
  print_endline ""


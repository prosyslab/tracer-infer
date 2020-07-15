module CFG = ProcCfg.Normal

let print_succ_nodes cfg = 
    let node = CFG.Node.underlying_node cfg in
    let preds_list = Procdesc.Node.get_succs node in
    Printf.printf "%s\n" (Location.to_string (CFG.Node.loc cfg));
    Stdlib.List.iteri (fun i n ->
      Printf.printf "%d %s\n" i (Location.to_string (CFG.Node.of_underlying_node n |> CFG.Node.loc))
    ) preds_list

type entry = {
  path: string;
  digest: string;
}

let digest_file (path : string) : string =
  Digest.to_hex (Digest.file path)

let load (cache_file : string) : entry list =
  if not (Sys.file_exists cache_file) then []
  else
    let ic = open_in cache_file in
    let entries = ref [] in
    (try
       while true do
         let line = input_line ic in
         if String.length line > 0 && line.[0] <> '#' then
           match String.split_on_char '\t' line with
           | [path; digest] -> entries := { path; digest } :: !entries
           | _ -> () (* skip malformed lines *)
       done
     with End_of_file -> ());
    close_in ic;
    List.rev !entries

let save (cache_file : string) (entries : entry list) : unit =
  let oc = open_out cache_file in
  List.iter (fun e ->
    Printf.fprintf oc "%s\t%s\n" e.path e.digest
  ) entries;
  close_out oc

let is_cached (entries : entry list) (replay_path : string) : bool =
  let current_digest = digest_file replay_path in
  List.exists (fun e -> e.path = replay_path && e.digest = current_digest) entries

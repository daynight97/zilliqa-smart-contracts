(***************************************************)
(*         Author: Starling Foundries LLC          *)
(***************************************************)
(***************************************************)
(*                 Scilla version                  *)
(***************************************************)
scilla_version 0
(***************************************************)
(*               Associated library                *)
(***************************************************)
import BoolUtils IntUtils
library MultisigLottery
    let one_msg = 
    fun (msg : Message) => 
    let nil_msg = Nil {Message} in
    Cons {Message} msg nil_msg
let two_msgs =
fun (msg1 : Message) =>
fun (msg2 : Message) =>
  let msgs_tmp = one_msg msg2 in
  Cons {Message} msg1 msgs_tmp
 let blk_leq =
  fun (blk1 : BNum) =>
  fun (blk2 : BNum) =>
    let bc1 = builtin blt blk1 blk2 in 
    let bc2 = builtin eq blk1 blk2 in 
    orb bc1 bc2

(* Given n > m, return [m+1; m+2; ...;n] *)
let iota : Uint128 -> Uint128 -> List Uint128 =
    fun (m : Uint128) => fun (n : Uint128) =>
      let m_lt_n = builtin lt m n in
      match m_lt_n with
      | True =>
          let delta = builtin sub n m in
          let delta_uint32_opt = builtin to_uint32 delta in
          let delta_uint32 =
            match delta_uint32_opt with
            | Some delta_uint32 => delta_uint32
            | None => Uint32 0
            end
          in
          let delta_nat = builtin to_nat delta_uint32 in
          let nil = Nil {Uint128} in
          let acc_init = Pair {(List Uint128) Uint128} nil n in
          let one = Uint128 1 in
          let step = fun (xs_n : Pair (List Uint128) Uint128) => fun (ignore : Nat) =>
            match xs_n with
            | Pair xs n =>
                let new_n = builtin sub n one in
                let new_xs = Cons {Uint128} new_n xs in
                Pair {(List Uint128) Uint128} new_xs new_n
            end in
          let fold = @nat_fold (Pair (List Uint128) Uint128) in
          let xs_m = fold step acc_init delta_nat in
          match xs_m with
          | Pair xs m => xs
          end
      | False => Nil {Uint128}
      end
  let zero = Uint128 0
  let one = Uint128 1
  let hundred = Uint128 100
  let incr = Uint32 1
  let false = False
  let true = True
  (* Error events *)
  type Error =
    | CodeInsufficientPayment
    | CodePotFull
    | CodeDrawingTooEarly
    | CodeContractLocked
    | CodeContractNotLocked
    | CodeRandomnessStale
    | CodeContractUnlocked
    | CodeNotAuthorized
    | CodeRandomError
    | CodeWinnerError
    | CodeRoundError
  let makeErrorEvent =
    fun (result : Error) =>
      let result_code = 
        match result with
        | CodeNotAuthorized       => Int32 -1
        | CodeInsufficientPayment => Int32 -2
        | CodePotFull             => Int32 -3
        | CodeDrawingTooEarly     => Int32 -4
        | CodeContractLocked      => Int32 -6
        | CodeContractNotLocked   => Int32 -7
        | CodeRandomnessStale     => Int32 -8
        | CodeContractUnlocked    => Int32 -9
        | CodeRandomError         => Int32 -10
        | CodeWinnerError         => Int32 -11
        | CodeRoundError          => Int32 -12
        end
      in
      { _eventname : "Error"; code : result_code }
(***************************************************)
(*             The contract definition             *)
(***************************************************)
contract UnlimitedLottery
(*  Parameters *)
(contract_owner : ByStr20,
 oracle         : ByStr20,
 ticket_price   : Uint128,
 pot_limit      : Uint128,
 owner_percent  : Uint128,
 name           : String)

with
builtin lt zero ticket_price
=>

(* Mutable fields *)
(*Tickets holds the map of indexed tickets for this drawing*)
field tickets: Map Uint128 ByStr20
                = Emp Uint128 ByStr20
(*Track the number of tickets sold this round*)
field tickets_size : Uint128 = Uint128 0
field max_tickets_size : Uint128 = builtin div pot_limit ticket_price 
(*Set to None once a winner has gotten their payment*)
field winner_percent: Uint128 = builtin sub hundred owner_percent
(*Store of counter of times the lottery has had a drawing*)
field drawing_number : Uint32 = Uint32 1
(*Last used randomness seed for deduplication check*)
field latest_seed : String = ""
field drand_round: Uint32 = Uint32 0
field full : Bool = false
field locked : Bool = false
(*Procedures*)
(* Emit Errors *)
procedure MakeError(err : Error)
  e = makeErrorEvent err;
  event e
end
procedure BroadcastFull()
    block_num <- & BLOCKNUMBER;
    full := true;
    e = {_eventname : "LotteryFull"; initiator : _sender; block: block_num};
    event e
end

procedure BroadcastDrawing( winner: ByStr20, winner_total: Uint128)
    block_num <- & BLOCKNUMBER;
    seed <- latest_seed;
    drand <- drand_round;
    full := false;
    e = {_eventname : "DrawingSuccess"; initiator : _sender; block: block_num; winner: winner; payout: winner_total; random: seed ; drand_round: drand};
    event e
end

  
procedure IsContractOwner()
  is_contract_owner = builtin eq contract_owner _sender;
  match is_contract_owner with
  | True => 
  | False =>
    err = CodeNotAuthorized;
    MakeError err
  end
end
procedure IsOracle()
  is_oracle = builtin eq oracle _sender;
  match is_oracle with
  | True => 
  | False =>
    err = CodeNotAuthorized;
    MakeError err
  end
end
procedure IsNotFull()
  full_status <- full;
  match full_status with
  | True => 
    err = CodePotFull;
    MakeError err
  | False =>
  end
end
procedure IsFull()
  full_status <- full;
  match full_status with
  | False => 
    err = CodeDrawingTooEarly;
    MakeError err
  | True =>
  end
end
procedure IsLocked()
  lock_status <- locked;
  match lock_status with
  | False => 
    err = CodeContractNotLocked;
    MakeError err
  | True =>
  end
end
procedure IsNotLocked()
  lock_status <- locked;
  match lock_status with
  | True => 
    err = CodeContractLocked;
    MakeError err
  | False =>
  end
end
procedure IsFreshRandomness(new_seed: String, new_round: Uint32)
  previous_seed <- latest_seed;
  stale = builtin eq previous_seed new_seed;
  match stale with
  | True => 
    err = CodeRandomnessStale;
    MakeError err
  | False =>
    current_round <- drand_round;
    round_increasing = builtin lt current_round new_round;
    match round_increasing with
    | False =>
      err = CodeRoundError;
      MakeError err
    | True =>
    end
  end
end

procedure Payout(winner: ByStr20, winner_total: Uint128, owner_total:Uint128)
    msg_to_winner = {_tag : "AdFunds"; _recipient : winner; _amount : winner_total};
    msg_to_owner = {_tag : "AddFunds"; _recipient : contract_owner; _amount : owner_total};
    msgs = two_msgs msg_to_winner msg_to_owner;
    send msgs
end

(*Call to draw a winner from the seed *)
(*clears the ticket fields and increments the blocks, drawing number*)
procedure DrawFromSeedAndClear(seed: String, round: Uint32)
  seed_int = builtin to_uint128 seed;
  total_tickets <- tickets_size;
  match seed_int with
  | Some drawing =>
    winning_ticket = builtin rem drawing total_tickets;
    winner <- tickets[winning_ticket];
    bal <- _balance;
    winner_pct <- winner_percent;
    tmp = builtin mul bal winner_pct;
    winner_cut = builtin div tmp hundred;
    owner_cut = builtin sub bal winner_cut;
    (*Clean up and ready for next round*)
    empty_map = Emp Uint128 ByStr20;
    tickets := empty_map;
    tickets_size := zero;
    drawing <- drawing_number;
    new_drawing = builtin add drawing incr;
    drawing_number := new_drawing;
    locked := false;
    latest_seed := seed;
    drand_round := round;
    (*Pay out*)
    match winner with
    | Some drawing_winner =>
      Payout drawing_winner winner_cut owner_cut;
      BroadcastDrawing drawing_winner winner_cut
    | None => 
      err = CodeWinnerError;
      MakeError err
    end
  | None => 
    err = CodeRandomError;
    MakeError err
  end
end
(*Mints a single ticket for the _sender by adding their address to the map at the specified index.*)
(*NOTE: for efficiency reasons it does not increment the total ticket size, this should be done manually after the call*)
procedure MintTicket(index: Uint128)
  tickets[index] := _sender
end
(*Creates and assigns the maximum number of tickets from the _amount to the sender*)
procedure TicketsForAddress()
    max_purchaseable_tickets = builtin div _amount ticket_price;
    no_tickets = builtin lt max_purchaseable_tickets one;
  match no_tickets with
  | False =>
    max_tickets_size_ <- max_tickets_size;
    (*Check that the tickets being sold don't overfill the pot*)
    start_ticket_index <- tickets_size;
    max_saleable_tickets = builtin sub max_tickets_size_ start_ticket_index;
    simple_sale = builtin lt max_purchaseable_tickets max_saleable_tickets;
    actual_tickets =
      match simple_sale with
      | False => max_saleable_tickets
      | True => max_purchaseable_tickets
      end;
    match simple_sale with
      | False => BroadcastFull
      | True => 
      end;
    total_cost = builtin mul actual_tickets ticket_price;
    remainder = builtin sub _amount total_cost;
    last_ticket = builtin add start_ticket_index actual_tickets;
    list_tickets = iota start_ticket_index last_ticket;
    forall list_tickets MintTicket;
    new_tickets_size = last_ticket;
    tickets_size := new_tickets_size;
    accept;
    (*Send the remaining funds if any to the _sender*)
    msg = { _tag : "AddFunds"; _recipient: _sender; _amount: remainder; tickets: actual_tickets };
    msgs = one_msg msg;
    send msgs
  | True =>
    err = CodeInsufficientPayment;
    MakeError err
    end
end

(*@dev: take an input drand seed and set the latest winner*)
transition Draw(seed: String, round: Uint32)
  IsOracle;
  IsLocked;
  DrawFromSeedAndClear seed round
end

(*Only lock the contract in anticipation of a drawing or in order to freeze a faulty contract *)
transition Lock(seed: String, round: Uint32)
  IsOracle;
  lock_status <- locked;
  match lock_status with 
  | True =>
    err = CodeContractLocked;
    MakeError err
  | False =>
  locked := true;
  drand_round := round;
  latest_seed := seed;
   e = {_eventname : "LockSuccess"; initiator : _sender; seed: seed};
    event e
  end
end
(*Manual unlock mechanism for testing *)
transition Unlock()
  IsOracle;
  lock_status <- locked;
  match lock_status with
  | False =>
    err = CodeContractUnlocked;
    MakeError err
  | True =>
    locked := false;
    e = {_eventname : "UnlockSuccess"; initiator : _sender};
    event e
  end
end
(* @dev:    Mint a new ticket for the _sender, any remaining funds will be left in sender's wallet*)
(* Returns error message CodeInsufficientPayment if the payment was too low for the tickets requested. *)
(*Note: this implementation allow for multiple tickets to be purchased in one transaction*)
transition AddFunds()
  IsNotLocked;
  IsNotFull;
  TicketsForAddress
end

(*@dev: intended for viral marketing to add a bonus to the next drawing round*)
transition ChargeUp()
  accept
end

------------------------ MODULE multiple_receivers --------------------------

EXTENDS Naturals, Sequences, TLC

(* --algorithm queue
variable queue = <<"first message", "second message">>;

\* Receive a message from the queue
macro recv(queue, receiver)
begin
  await queue # <<>>;
  receiver := Head(queue);
  queue := Tail(queue);
end macro

process handler \in 1..2
variable msg = "";
begin loop:
  while TRUE do
    recv(queue, msg);
  end while
end process

end algorithm *)

=============================================================================
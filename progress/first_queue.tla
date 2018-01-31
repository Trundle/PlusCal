---------------------------- MODULE first_queue -----------------------------

EXTENDS Sequences, TLC

(* --algorithm queue
variable queue = <<"first message", "second message">>,
  msg = "";

\* Receive a message from the queue
macro recv(queue, receiver)
begin
  await queue # <<>>;
  receiver := Head(queue);
  queue := Tail(queue);
end macro

begin
  recv(queue, msg);
  print msg;
  recv(queue, msg);
  print msg;

end algorithm *)

=============================================================================
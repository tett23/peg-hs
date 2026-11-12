# Compare the terminal IDs observed at Happy's lexer callback with the IDs
# shifted by the parser. EOF (159) is not sent through the ordinary callback;
# the parser can synthesize the error token (0) to close a layout context.
BEGIN {
  callbackCount = 0
  shiftCount = 0
  if (callbacks == "" || shifts == "") {
    print "set callbacks and shifts output paths" > "/dev/stderr"
    exit 2
  }
}
/^LEXID [0-9]+$/ {
  id = $2
  if (id == 0 || id == 159) {
    print "unexpected synthetic or EOF callback ID: " id > "/dev/stderr"
    bad = 1
  }
  seen[++callbackCount] = id
  print id > callbacks
}
/action: shift, enter state/ {
  id = $0
  sub(/^.*state: [0-9]+,[[:space:]]*token: /, "", id)
  sub(/,.*/, "", id)
  if (id !~ /^[0-9]+$/) {
    print "cannot read shift ID: " $0 > "/dev/stderr"
    bad = 1
    next
  }
  if (id == 0) next
  print id > shifts
  shiftCount++
  if (!bad && (shiftCount > callbackCount || id != seen[shiftCount])) {
    print "lexer/shift mismatch at position " shiftCount ": callback=" seen[shiftCount] ", shift=" id > "/dev/stderr"
    bad = 1
  }
}
END {
  if (callbackCount != shiftCount) {
    print "lexer/shift count mismatch: callback=" callbackCount ", shift=" shiftCount > "/dev/stderr"
    bad = 1
  }
  if (bad) exit 1
}

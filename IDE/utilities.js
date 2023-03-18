const assertThat = (x, message="No message") => {
  if (!x) throw new Error("Assertion failed: " + message);
};


const assert = {
  call: assertThat,
  that: assertThat,
  deepEqual: (x, y, message=null) => {
    if (x !== y) {
      if (message === null) {
        message = `Expected ${x} to equal ${y}`;
      } else {
        message = `Expected ${x} to equal ${y}: ${message}`;
      }
      throw new Error("Assertion failed: " + message);
    }
  }
};

module.exports = {
    assert,
};

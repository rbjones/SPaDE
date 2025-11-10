# Python ABC Coding Standards

**Document ID**: amms008.md  
**Category**: Methods and Standards  
**Subsystem**: docs/admin (am)  
**Applies To**: All Python Abstract Base Class implementations

## Overview

This document defines standards and patterns for implementing Python Abstract Base Classes (ABCs) in the SPaDE project. ABCs define interfaces that concrete implementations must fulfill, ensuring consistency and enabling polymorphism.

## When to Use ABCs

Use ABCs when:

- Defining interfaces for multiple implementations
- Ensuring subclasses implement required methods
- Documenting expected behavior without implementation
- Enabling dependency injection and testing with mocks

## File Naming Convention

- ABC definitions: `<subsystem>cd<nnn>.py` (e.g., `krcd008.py`)
- Concrete implementations: `<subsystem>cd<nnn+1>.py` (e.g., `krcd009.py`)
- Tests for ABC: `test_<abc_file>.py` (e.g., `test_krcd008.py`)
- Tests for implementation: `test_<impl_file>.py` (e.g., `test_krcd009.py`)

## Makefile Integration

Once ABC files are created, add them to the subsystem makefile for automatic testing:

1. Add ABC filename to `PYABCFILES` variable in `<subsystem>ci001.mkf`
2. Test files are automatically derived: `test_<abc>.py`
3. Run tests: `make -f <subsystem>ci001.mkf test`

Example for `kr/krcd008.py`:

```makefile
PYABCFILES = krcd008.py
```

The makefile will automatically:

- Validate Python syntax with `python -m py_compile`
- Run pytest on all ABC test files
- Report results

## Required Imports

```python
from abc import ABC, abstractmethod
```

For type hints:

```python
from typing import Optional, Union  # As needed
```

## ABC Structure Template

```python
"""Module docstring explaining purpose and context.

References to relevant design documents.
"""

from abc import ABC, abstractmethod


class MyInterface(ABC):
    """Class docstring describing the interface.
    
    Explain what this interface represents and its role in the system.
    List key responsibilities or concepts.
    """
    
    @abstractmethod
    def required_method(self, param: type) -> return_type:
        """Method docstring following Google style.
        
        Detailed description of what the method should do.
        Explain any important concepts or constraints.
        
        Args:
            param: Description of parameter including valid values/ranges
            
        Returns:
            Description of return value and its meaning
            
        Raises:
            ExceptionType: When and why this exception is raised
        """
        pass
```

## Docstring Standards

### Module Level

```python
"""Brief one-line description.

Longer explanation if needed, including:
- Purpose of this module
- References to design documents
- Relationship to other modules
"""
```

### Class Level

```python
"""Brief one-line description of the interface.

Detailed explanation including:
- What this interface represents
- Key responsibilities
- Important concepts or terminology
- Examples of intended use (optional)
"""
```

### Method Level (Google Style)

```python
"""Brief one-line summary of what the method does.

Detailed explanation including:
- Algorithm or approach (if relevant to interface contract)
- Pre-conditions and post-conditions
- Side effects (if any)
- Thread safety (if relevant)

Args:
    param_name: Description including type constraints, valid ranges,
        special values (like None), and their meanings. Use multiple
        lines if needed with proper indentation.
    another_param: Description

Returns:
    Description of return value including:
    - Type and structure
    - Meaning of different values
    - None if applicable

Raises:
    ValueError: When parameter validation fails
    IOError: When file operations fail
    
Examples:
    >>> obj.method(arg1, arg2)
    expected_result
"""
```

## Type Hints

All abstract methods must include type hints for:

- All parameters
- Return values
- Use `Optional[type]` for values that can be None
- Use `Union[type1, type2]` for multiple possible types
- Use `list[type]` (Python 3.9+) or `List[type]` (earlier) for lists

Examples:

```python
def simple_method(self, data: bytes) -> int:
    """Returns count of bytes."""
    pass

def optional_return(self, key: str) -> Optional[bytes]:
    """Returns bytes if found, None otherwise."""
    pass

def union_return(self, data: bytes) -> tuple[str, Optional[bytes]]:
    """Returns tuple of (type_name, optional_data)."""
    pass
```

## Common Patterns

### Read/Write Operations

```python
@abstractmethod
def read(self, source: str) -> bytes:
    """Read data from source.
    
    Args:
        source: Path or identifier for data source
        
    Returns:
        Data read from source
        
    Raises:
        FileNotFoundError: If source doesn't exist
        IOError: If read operation fails
    """
    pass

@abstractmethod
def write(self, data: bytes, destination: str) -> None:
    """Write data to destination.
    
    Args:
        data: Bytes to write
        destination: Path or identifier for destination
        
    Raises:
        IOError: If write operation fails
    """
    pass
```

### Resource Management

```python
@abstractmethod
def open(self, resource: str) -> None:
    """Open resource for use.
    
    Must call close() when done.
    """
    pass

@abstractmethod
def close(self) -> None:
    """Close resource and release handles.
    
    Safe to call multiple times.
    """
    pass
```

### Query Operations

```python
@abstractmethod
def get_by_id(self, item_id: int) -> Optional[bytes]:
    """Retrieve item by ID.
    
    Args:
        item_id: Identifier for item
        
    Returns:
        Item data if found, None otherwise
    """
    pass

@abstractmethod
def exists(self, item_id: int) -> bool:
    """Check if item exists.
    
    Args:
        item_id: Identifier to check
        
    Returns:
        True if item exists, False otherwise
    """
    pass
```

## Testing Requirements

Every ABC must have accompanying tests in `test_<abc_file>.py`:

### 1. Instantiation Test

```python
def test_cannot_instantiate():
    """Verify ABC cannot be instantiated directly."""
    with pytest.raises(TypeError):
        MyInterface()
```

### 2. Method Existence Tests

```python
def test_has_required_methods():
    """Verify all required abstract methods are defined."""
    required_methods = ['method1', 'method2', 'method3']
    for method in required_methods:
        assert hasattr(MyInterface, method)
        assert callable(getattr(MyInterface, method))
```

### 3. Inheritance Test (Optional)

```python
def test_concrete_implementation():
    """Verify concrete class can implement interface."""
    class ConcreteImpl(MyInterface):
        def method1(self, param: type) -> return_type:
            return expected_value
            
    obj = ConcreteImpl()
    assert isinstance(obj, MyInterface)
```

## Validation Checklist

Before considering an ABC complete:

- [ ] All methods have `@abstractmethod` decorator
- [ ] All parameters have type hints
- [ ] All return values have type hints
- [ ] Module has docstring with references to design docs
- [ ] Each class has comprehensive docstring
- [ ] Each method has detailed docstring (Args, Returns, Raises)
- [ ] Test file exists with minimum required tests
- [ ] ABC file added to `PYABCFILES` in subsystem makefile
- [ ] All tests pass: `make -f <subsystem>ci001.mkf test`
- [ ] Follows PEP 8: `flake8 <abc_file>.py` (if available)
- [ ] Type checking passes: `mypy <abc_file>.py` (if available)

## Common Mistakes to Avoid

### ❌ Missing @abstractmethod

```python
class BadInterface(ABC):
    def method(self):  # Missing @abstractmethod
        pass
```

### ✅ Correct

```python
class GoodInterface(ABC):
    @abstractmethod
    def method(self):
        pass
```

### ❌ Implementing in ABC

```python
class BadInterface(ABC):
    @abstractmethod
    def method(self):
        return "implemented"  # Should not implement
```

### ✅ Correct

```python
class GoodInterface(ABC):
    @abstractmethod
    def method(self):
        pass  # No implementation
```

### ❌ Missing Type Hints

```python
@abstractmethod
def method(self, data):  # No type hints
    pass
```

### ✅ Correct

```python
@abstractmethod
def method(self, data: bytes) -> int:
    pass
```

## Python Version Requirements

- **Minimum**: Python 3.11
- Use modern type hint syntax: `list[str]` not `List[str]`
- Use `|` for unions: `str | None` not `Optional[str]` (when clarity allows)

## References

- [PEP 3119 - Introducing Abstract Base Classes](https://www.python.org/dev/peps/pep-3119/)
- [Python abc module documentation](https://docs.python.org/3/library/abc.html)
- [Google Python Style Guide - Docstrings](https://google.github.io/styleguide/pyguide.html#38-comments-and-docstrings)

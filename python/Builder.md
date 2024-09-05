```
let tcm_types = data
    .sim_message
    .tcm_types
    .as_ref()
    .map(|tcms| {
        let mut tokens = String::new();
        for tcm in tcms {
            let _ = write!(&mut tokens, "{},", tcm);
        }
        tokens
    })
    .unwrap_or("None".to_string());
doc.add_text(tcm_kind_field, tcm_types);

let products_installed = data
    .sim_message
    .products_installed
    .as_ref()
    .map(|products| {
        let mut tokens = String::new();
        for product in products {
            let _ = write!(&mut tokens, "{},", product);
        }
        tokens
    })
    .unwrap_or("None".to_string());
doc.add_text(products_installed_field, products_installed);

.as_ref() in products_installed is underlined red. It is saying this error:
type annotations neededrustcClick for full compiler diagnostic
mod.rs(286, 14): type must be known at this point
mod.rs(282, 34): try using a fully qualified path to specify the expected types: `<std::vec::Vec<sim_message::Product> as AsRef<T>>::as_ref(&`, `)`
core::convert::AsRef
pub trait AsRef<T>
pub fn as_ref(&self) -> &T
where
    // Bounds from trait:
    T: ?Sized,
Converts this type into a shared reference of the (usually inferred) input type.
```

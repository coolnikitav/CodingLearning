```
I have a vector of installed products. Since it was built from a hasmap, its unordered. I want to sort this vector by the enumerated value, since enum have an actual count attached to them.

pub fn collect_installed_products(
    product_ini_locations: &HashMap<String, String>,
) -> Result<Vec<Product>, anyhow::Error> {
    log::debug!("Entered collect_installed_products");
    let mut installed_products = Vec::with_capacity(product_ini_locations.len());

    for (product_name, product_ini_location) in product_ini_locations.iter() {
        let product_result = add_product(product_name, product_ini_location);
        // If ini file is not found, handle it and continue execution
        match product_result {
            Ok(product) => installed_products.push(product),
            Err(error) => log::debug!("Error opening ini file: {}", error),
        }   
    }
    // sort installed_products by productName here
    Ok(installed_products)
}

#[derive(Serialize, Deserialize, Debug, Clone, PartialEq)]
pub enum ProductName {
    Commercial,
    CentralDriveEV,
    OffHighway,
    Defense,
    AcromagIntegration,
    TCMSelfTest,
    Addons,
    SupportApps,
    Unknown,
}
```

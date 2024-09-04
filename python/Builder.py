I also have this in sim_message:

impl ProductName {
    pub fn as_string(&self) -> &str {
        match &self {
            ProductName::Commercial => "Commercial",
            ProductName::CentralDriveEV => "CentralDriveEV",
            ProductName::OffHighway => "OffHighway",
            ProductName::Defense => "Defense",
            ProductName::AcromagIntegration => "AcromagIntegration",
            ProductName::TCMSelfTest => "TCMSelfTest",
            ProductName::Addons => "Addons",
            ProductName::SupportApps => "SupportApps",
            ProductName::Unknown => "Unknown",
        }
    }
}

However, when I try using it in sim_client, I get an error:
let product_name = match product_name {
        ProductName::Commercial.as_string() => ProductName::Commercial,

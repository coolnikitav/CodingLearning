```
impl Display for ProductName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProductName::Commercial         => write!(f, "Commercial"),
            ProductName::CentralDriveEV     => write!(f, "CentralDriveEV"),
            ProductName::OffHighway         => write!(f, "OffHighway"),
            ProductName::Defense            => write!(f, "Defense"),
            ProductName::AcromagIntegration => write!(f, "AcromagIntegration"),
            ProductName::TCMSelfTest        => write!(f, "TCMSelfTest"),
            ProductName::Addons             => write!(f, "Addons"),
            ProductName::SupportApps        => write!(f, "SupportApps"),
            ProductName::Unknown            => write!(f, "Unknown"),
        }
    }
}
```

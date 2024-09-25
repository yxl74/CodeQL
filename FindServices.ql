import java
import semmle.code.java.dataflow.DataFlow
import semmle.code.xml.AndroidManifest

/** Service Class */
class ServiceClass extends RefType {
    ServiceClass() {
        this.getASupertype*().hasQualifiedName("android.os", "IInterface")
    }
}

/** Holds if the service is statically declared in AndroidManifest.xml */
predicate isStaticallyDeclaredService(ServiceClass service, AndroidComponentXmlElement svc) {
    svc instanceof AndroidServiceXmlElement and
    svc.getComponentName() = ["." + service.getName(), service.getQualifiedName()]
}

/** A method that registers a service dynamically */
class AddServiceMethod extends Method {
    AddServiceMethod() {
        this.getDeclaringType().hasQualifiedName("android.os", "ServiceManager") and
        this.hasName("addService")
    }
}

/** Holds if the service is dynamically registered using ServiceManager.addService */
predicate isDynamicallyRegisteredService(ServiceClass service, MethodAccess ma) {
    exists(AddServiceMethod m |
        ma.getMethod() = m and
        (
            ma.getArgument(1).(ClassInstanceExpr).getConstructedType() = service
            or
            exists(Variable v |
                v.getType() = service and ma.getArgument(1) = v.getAnAccess()
            )
        )
    )
}

from ServiceClass service, string registrationType, string location, string serviceName
where 
    (
        exists(AndroidComponentXmlElement svc | 
            isStaticallyDeclaredService(service, svc) and
            registrationType = "statically" and
            location = svc.getFile().getAbsolutePath() and
            serviceName = svc.getComponentName()
        )
        or
        exists(MethodAccess ma |
            isDynamicallyRegisteredService(service, ma) and
            registrationType = "dynamically" and
            location = ma.getFile().getAbsolutePath() and
            serviceName = ma.getArgument(0).(StringLiteral).getValue()
        )
    )
select
    service.getQualifiedName(),
    registrationType,
    serviceName,
    "Registered " + registrationType + " at " + location
